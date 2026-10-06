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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_525_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_526_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_528_, 11, v___x_525_);
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
lean_object* v___x_546_; lean_object* v_toCold_547_; lean_object* v_env_548_; lean_object* v_options_549_; uint8_t v___x_550_; lean_object* v_env_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_546_ = lean_st_ref_get(v___y_544_);
v_toCold_547_ = lean_ctor_get(v___y_543_, 0);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_546_);
v_options_549_ = lean_ctor_get(v_toCold_547_, 2);
v___x_550_ = 0;
v_env_551_ = l_Lean_Environment_setRecordingDeps(v_env_548_, v___x_550_);
v___x_552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2);
v___x_553_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_549_);
v___x_554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_554_, 0, v_env_551_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
lean_ctor_set(v___x_554_, 3, v_options_549_);
v___x_555_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_msgData_542_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___boxed(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msgData_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_ref_566_; lean_object* v___x_567_; lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_ref_566_ = lean_ctor_get(v___y_563_, 2);
v___x_567_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msg_562_, v___y_563_, v___y_564_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_inc(v_ref_566_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_ref_566_);
lean_ctor_set(v___x_572_, 1, v_a_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 1);
lean_ctor_set(v___x_570_, 0, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg___boxed(lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_docComment_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_____x_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___x_595_; 
v___x_595_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_582_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_596_, v_a_583_, v_a_584_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; 
v_a_606_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_595_, 1);
v_____x_587_ = v_a_606_;
v___y_588_ = v_a_583_;
v___y_589_ = v_a_584_;
goto v___jp_586_;
}
v___jp_586_:
{
lean_object* v_snd_590_; lean_object* v_fst_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_594_; 
v_snd_590_ = lean_ctor_get(v_____x_587_, 1);
lean_inc(v_snd_590_);
v_fst_591_ = lean_ctor_get(v_____x_587_, 0);
lean_inc(v_fst_591_);
lean_dec_ref(v_____x_587_);
v_fst_592_ = lean_ctor_get(v_snd_590_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v_snd_590_, 1);
lean_inc(v_snd_593_);
lean_dec(v_snd_590_);
v___x_594_ = l_Lean_parseVersoDocStringAt(v_fst_591_, v_fst_592_, v_snd_593_, v___y_588_, v___y_589_);
lean_dec(v_fst_591_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___boxed(lean_object* v_docComment_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_parseVersoDocString(v_docComment_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_docComment_607_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_object* v_00_u03b1_612_, lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_613_, v___y_614_, v___y_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___boxed(lean_object* v_00_u03b1_618_, lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(v_00_u03b1_618_, v_msg_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_view_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_____x_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___x_654_; 
v___x_654_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_624_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_655_, v_a_625_, v_a_626_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_654_, 1);
v_____x_629_ = v_a_665_;
v___y_630_ = v_a_625_;
v___y_631_ = v_a_626_;
goto v___jp_628_;
}
v___jp_628_:
{
lean_object* v_snd_632_; lean_object* v_fst_633_; lean_object* v_fst_634_; lean_object* v_snd_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_snd_632_ = lean_ctor_get(v_____x_629_, 1);
lean_inc(v_snd_632_);
v_fst_633_ = lean_ctor_get(v_____x_629_, 0);
lean_inc(v_fst_633_);
lean_dec_ref(v_____x_629_);
v_fst_634_ = lean_ctor_get(v_snd_632_, 0);
lean_inc(v_fst_634_);
v_snd_635_ = lean_ctor_get(v_snd_632_, 1);
lean_inc(v_snd_635_);
lean_dec(v_snd_632_);
v___x_636_ = lean_box(0);
v___x_637_ = l_Lean_parseVersoDocStringAt(v_fst_633_, v_fst_634_, v_snd_635_, v___y_630_, v___y_631_);
lean_dec(v_fst_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___x_637_, 0);
lean_dec(v_unused_645_);
v___x_639_ = v___x_637_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_dec(v___x_637_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_636_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_636_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_a_646_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_637_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_637_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_view_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_reportVersoParseFailure(v_view_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec_ref(v_view_666_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_671_, lean_object* v_declName_672_, lean_object* v_binders_673_, lean_object* v___x_674_, uint8_t v___x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_671_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Doc_DocM_exec___redArg(v_declName_672_, v_binders_673_, v___x_674_, v___x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_683_;
}
else
{
lean_object* v_toCold_684_; lean_object* v_val_685_; lean_object* v_currRecDepth_686_; lean_object* v_ref_687_; uint16_t v_optionFlags_688_; uint8_t v_suppressElabErrors_689_; uint8_t v_isRecordingDeps_690_; lean_object* v_fileName_691_; lean_object* v_options_692_; lean_object* v_maxRecDepth_693_; lean_object* v_currNamespace_694_; lean_object* v_openDecls_695_; lean_object* v_initHeartbeats_696_; lean_object* v_maxHeartbeats_697_; lean_object* v_quotContext_698_; lean_object* v_currMacroScope_699_; lean_object* v_cancelTk_x3f_700_; lean_object* v_inheritedTraceOptions_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_toCold_684_ = lean_ctor_get(v___y_680_, 0);
v_val_685_ = lean_ctor_get(v_fileMap_x3f_671_, 0);
v_currRecDepth_686_ = lean_ctor_get(v___y_680_, 1);
v_ref_687_ = lean_ctor_get(v___y_680_, 2);
v_optionFlags_688_ = lean_ctor_get_uint16(v___y_680_, sizeof(void*)*3);
v_suppressElabErrors_689_ = lean_ctor_get_uint8(v___y_680_, sizeof(void*)*3 + 2);
v_isRecordingDeps_690_ = lean_ctor_get_uint8(v___y_680_, sizeof(void*)*3 + 3);
v_fileName_691_ = lean_ctor_get(v_toCold_684_, 0);
v_options_692_ = lean_ctor_get(v_toCold_684_, 2);
v_maxRecDepth_693_ = lean_ctor_get(v_toCold_684_, 3);
v_currNamespace_694_ = lean_ctor_get(v_toCold_684_, 4);
v_openDecls_695_ = lean_ctor_get(v_toCold_684_, 5);
v_initHeartbeats_696_ = lean_ctor_get(v_toCold_684_, 6);
v_maxHeartbeats_697_ = lean_ctor_get(v_toCold_684_, 7);
v_quotContext_698_ = lean_ctor_get(v_toCold_684_, 8);
v_currMacroScope_699_ = lean_ctor_get(v_toCold_684_, 9);
v_cancelTk_x3f_700_ = lean_ctor_get(v_toCold_684_, 10);
v_inheritedTraceOptions_701_ = lean_ctor_get(v_toCold_684_, 11);
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
lean_inc(v_val_685_);
lean_inc_ref(v_fileName_691_);
v___x_702_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_702_, 0, v_fileName_691_);
lean_ctor_set(v___x_702_, 1, v_val_685_);
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
lean_inc(v_ref_687_);
lean_inc(v_currRecDepth_686_);
v___x_703_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_currRecDepth_686_);
lean_ctor_set(v___x_703_, 2, v_ref_687_);
lean_ctor_set_uint16(v___x_703_, sizeof(void*)*3, v_optionFlags_688_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*3 + 2, v_suppressElabErrors_689_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*3 + 3, v_isRecordingDeps_690_);
v___x_704_ = l_Lean_Doc_DocM_exec___redArg(v_declName_672_, v_binders_673_, v___x_674_, v___x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___x_703_, v___y_681_);
lean_dec_ref_known(v___x_703_, 3);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_705_, lean_object* v_declName_706_, lean_object* v_binders_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v___x_9836__boxed_717_; lean_object* v_res_718_; 
v___x_9836__boxed_717_ = lean_unbox(v___x_709_);
v_res_718_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_705_, v_declName_706_, v_binders_707_, v___x_708_, v___x_9836__boxed_717_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_775_, uint8_t v___y_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 1)
{
lean_object* v_pre_778_; 
v_pre_778_ = lean_ctor_get(v_x_777_, 0);
switch(lean_obj_tag(v_pre_778_))
{
case 1:
{
lean_object* v_pre_779_; 
v_pre_779_ = lean_ctor_get(v_pre_778_, 0);
switch(lean_obj_tag(v_pre_779_))
{
case 0:
{
lean_object* v_str_780_; lean_object* v_str_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_str_780_ = lean_ctor_get(v_x_777_, 1);
v_str_781_ = lean_ctor_get(v_pre_778_, 1);
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_783_ = lean_string_dec_eq(v_str_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_785_ = lean_string_dec_eq(v_str_781_, v___x_784_);
if (v___x_785_ == 0)
{
return v___x_785_;
}
else
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_787_ = lean_string_dec_eq(v_str_780_, v___x_786_);
if (v___x_787_ == 0)
{
return v___x_787_;
}
else
{
return v_suppressElabErrors_775_;
}
}
}
else
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_789_ = lean_string_dec_eq(v_str_780_, v___x_788_);
if (v___x_789_ == 0)
{
return v___x_789_;
}
else
{
return v_suppressElabErrors_775_;
}
}
}
case 1:
{
lean_object* v_pre_790_; 
v_pre_790_ = lean_ctor_get(v_pre_779_, 0);
if (lean_obj_tag(v_pre_790_) == 0)
{
lean_object* v_str_791_; lean_object* v_str_792_; lean_object* v_str_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_str_791_ = lean_ctor_get(v_x_777_, 1);
v_str_792_ = lean_ctor_get(v_pre_778_, 1);
v_str_793_ = lean_ctor_get(v_pre_779_, 1);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_795_ = lean_string_dec_eq(v_str_793_, v___x_794_);
if (v___x_795_ == 0)
{
return v___x_795_;
}
else
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_797_ = lean_string_dec_eq(v_str_792_, v___x_796_);
if (v___x_797_ == 0)
{
return v___x_797_;
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_799_ = lean_string_dec_eq(v_str_791_, v___x_798_);
if (v___x_799_ == 0)
{
return v___x_799_;
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
return v___y_776_;
}
}
default: 
{
return v___y_776_;
}
}
}
case 0:
{
lean_object* v_str_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_str_800_ = lean_ctor_get(v_x_777_, 1);
v___x_801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_802_ = lean_string_dec_eq(v_str_800_, v___x_801_);
if (v___x_802_ == 0)
{
return v___x_802_;
}
else
{
return v_suppressElabErrors_775_;
}
}
default: 
{
return v___y_776_;
}
}
}
else
{
return v___y_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_803_, lean_object* v___y_804_, lean_object* v_x_805_){
_start:
{
uint8_t v_suppressElabErrors_boxed_806_; uint8_t v___y_9929__boxed_807_; uint8_t v_res_808_; lean_object* v_r_809_; 
v_suppressElabErrors_boxed_806_ = lean_unbox(v_suppressElabErrors_803_);
v___y_9929__boxed_807_ = lean_unbox(v___y_804_);
v_res_808_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_806_, v___y_9929__boxed_807_, v_x_805_);
lean_dec(v_x_805_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_810_, lean_object* v_msgData_811_, uint8_t v_severity_812_, uint8_t v_isSilent_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v___y_826_; lean_object* v_toCold_827_; lean_object* v___y_828_; lean_object* v___y_857_; lean_object* v___y_858_; uint8_t v___y_859_; lean_object* v___y_860_; uint8_t v___y_861_; lean_object* v___y_862_; uint8_t v___y_863_; lean_object* v___y_864_; lean_object* v___y_884_; lean_object* v___y_885_; uint8_t v___y_886_; uint8_t v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; lean_object* v___y_890_; uint8_t v___y_894_; uint8_t v___y_895_; uint8_t v___y_896_; uint8_t v___x_907_; uint8_t v___y_909_; uint8_t v___y_910_; uint8_t v___y_911_; uint8_t v___y_913_; uint8_t v___x_921_; 
v___x_907_ = 2;
v___x_921_ = l_Lean_instBEqMessageSeverity_beq(v_severity_812_, v___x_907_);
if (v___x_921_ == 0)
{
v___y_913_ = v___x_921_;
goto v___jp_912_;
}
else
{
uint8_t v___x_922_; 
lean_inc_ref(v_msgData_811_);
v___x_922_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_811_);
v___y_913_ = v___x_922_;
goto v___jp_912_;
}
v___jp_819_:
{
lean_object* v_currNamespace_829_; lean_object* v_openDecls_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_env_835_; lean_object* v_nextMacroScope_836_; lean_object* v_ngen_837_; lean_object* v_auxDeclNGen_838_; lean_object* v_traceState_839_; lean_object* v_cache_840_; lean_object* v_recordedDeps_841_; lean_object* v_messages_842_; lean_object* v_infoState_843_; lean_object* v_snapshotTasks_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_855_; 
v_currNamespace_829_ = lean_ctor_get(v_toCold_827_, 4);
v_openDecls_830_ = lean_ctor_get(v_toCold_827_, 5);
lean_inc(v_openDecls_830_);
lean_inc(v_currNamespace_829_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_currNamespace_829_);
lean_ctor_set(v___x_831_, 1, v_openDecls_830_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___y_823_);
lean_inc_ref(v___y_825_);
lean_inc_ref(v___y_822_);
v___x_833_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_833_, 0, v___y_822_);
lean_ctor_set(v___x_833_, 1, v___y_824_);
lean_ctor_set(v___x_833_, 2, v___y_821_);
lean_ctor_set(v___x_833_, 3, v___y_825_);
lean_ctor_set(v___x_833_, 4, v___x_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*5, v___y_820_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*5 + 1, v___y_826_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*5 + 2, v_isSilent_813_);
v___x_834_ = lean_st_ref_take(v___y_828_);
v_env_835_ = lean_ctor_get(v___x_834_, 0);
v_nextMacroScope_836_ = lean_ctor_get(v___x_834_, 1);
v_ngen_837_ = lean_ctor_get(v___x_834_, 2);
v_auxDeclNGen_838_ = lean_ctor_get(v___x_834_, 3);
v_traceState_839_ = lean_ctor_get(v___x_834_, 4);
v_cache_840_ = lean_ctor_get(v___x_834_, 5);
v_recordedDeps_841_ = lean_ctor_get(v___x_834_, 6);
v_messages_842_ = lean_ctor_get(v___x_834_, 7);
v_infoState_843_ = lean_ctor_get(v___x_834_, 8);
v_snapshotTasks_844_ = lean_ctor_get(v___x_834_, 9);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_855_ == 0)
{
v___x_846_ = v___x_834_;
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_snapshotTasks_844_);
lean_inc(v_infoState_843_);
lean_inc(v_messages_842_);
lean_inc(v_recordedDeps_841_);
lean_inc(v_cache_840_);
lean_inc(v_traceState_839_);
lean_inc(v_auxDeclNGen_838_);
lean_inc(v_ngen_837_);
lean_inc(v_nextMacroScope_836_);
lean_inc(v_env_835_);
lean_dec(v___x_834_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = lean_box(0);
v___x_849_ = l_Lean_MessageLog_add(v___x_833_, v_messages_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 7, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_env_835_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_nextMacroScope_836_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_ngen_837_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_auxDeclNGen_838_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v_traceState_839_);
lean_ctor_set(v_reuseFailAlloc_854_, 5, v_cache_840_);
lean_ctor_set(v_reuseFailAlloc_854_, 6, v_recordedDeps_841_);
lean_ctor_set(v_reuseFailAlloc_854_, 7, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_854_, 8, v_infoState_843_);
lean_ctor_set(v_reuseFailAlloc_854_, 9, v_snapshotTasks_844_);
v___x_851_ = v_reuseFailAlloc_854_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_st_ref_put(v___y_828_, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_848_);
return v___x_853_;
}
}
}
v___jp_856_:
{
lean_object* v_fileName_865_; lean_object* v_fileMap_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
v_fileName_865_ = lean_ctor_get(v___y_860_, 0);
v_fileMap_866_ = lean_ctor_get(v___y_860_, 1);
v___x_867_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_811_);
v___x_868_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_867_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_882_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_inc_ref_n(v_fileMap_866_, 2);
v___x_873_ = l_Lean_FileMap_toPosition(v_fileMap_866_, v___y_862_);
lean_dec(v___y_862_);
v___x_874_ = l_Lean_FileMap_toPosition(v_fileMap_866_, v___y_864_);
lean_dec(v___y_864_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_861_ == 0)
{
lean_del_object(v___x_871_);
lean_dec_ref(v___y_857_);
v___y_820_ = v___y_859_;
v___y_821_ = v___x_875_;
v___y_822_ = v_fileName_865_;
v___y_823_ = v_a_869_;
v___y_824_ = v___x_873_;
v___y_825_ = v___x_876_;
v___y_826_ = v___y_863_;
v_toCold_827_ = v___y_858_;
v___y_828_ = v___y_817_;
goto v___jp_819_;
}
else
{
uint8_t v___x_877_; 
lean_inc(v_a_869_);
v___x_877_ = l_Lean_MessageData_hasTag(v___y_857_, v_a_869_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_dec_ref_known(v___x_875_, 1);
lean_dec_ref(v___x_873_);
lean_dec(v_a_869_);
v___x_878_ = lean_box(0);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_878_);
v___x_880_ = v___x_871_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_del_object(v___x_871_);
v___y_820_ = v___y_859_;
v___y_821_ = v___x_875_;
v___y_822_ = v_fileName_865_;
v___y_823_ = v_a_869_;
v___y_824_ = v___x_873_;
v___y_825_ = v___x_876_;
v___y_826_ = v___y_863_;
v_toCold_827_ = v___y_858_;
v___y_828_ = v___y_817_;
goto v___jp_819_;
}
}
}
}
v___jp_883_:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Syntax_getTailPos_x3f(v___y_888_, v___y_887_);
lean_dec(v___y_888_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_inc(v___y_890_);
v___y_857_ = v___y_884_;
v___y_858_ = v___y_885_;
v___y_859_ = v___y_887_;
v___y_860_ = v___y_885_;
v___y_861_ = v___y_886_;
v___y_862_ = v___y_890_;
v___y_863_ = v___y_889_;
v___y_864_ = v___y_890_;
goto v___jp_856_;
}
else
{
lean_object* v_val_892_; 
v_val_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v___x_891_, 1);
v___y_857_ = v___y_884_;
v___y_858_ = v___y_885_;
v___y_859_ = v___y_887_;
v___y_860_ = v___y_885_;
v___y_861_ = v___y_886_;
v___y_862_ = v___y_890_;
v___y_863_ = v___y_889_;
v___y_864_ = v_val_892_;
goto v___jp_856_;
}
}
v___jp_893_:
{
lean_object* v_toCold_897_; lean_object* v_ref_898_; uint8_t v_suppressElabErrors_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v_ref_903_; lean_object* v___x_904_; 
v_toCold_897_ = lean_ctor_get(v___y_816_, 0);
v_ref_898_ = lean_ctor_get(v___y_816_, 2);
v_suppressElabErrors_899_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*3 + 2);
v___x_900_ = lean_box(v_suppressElabErrors_899_);
v___x_901_ = lean_box(v___y_894_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_902_, 0, v___x_900_);
lean_closure_set(v___f_902_, 1, v___x_901_);
v_ref_903_ = l_Lean_replaceRef(v_ref_810_, v_ref_898_);
v___x_904_ = l_Lean_Syntax_getPos_x3f(v_ref_903_, v___y_895_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___y_884_ = v___f_902_;
v___y_885_ = v_toCold_897_;
v___y_886_ = v_suppressElabErrors_899_;
v___y_887_ = v___y_895_;
v___y_888_ = v_ref_903_;
v___y_889_ = v___y_896_;
v___y_890_ = v___x_905_;
goto v___jp_883_;
}
else
{
lean_object* v_val_906_; 
v_val_906_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_904_, 1);
v___y_884_ = v___f_902_;
v___y_885_ = v_toCold_897_;
v___y_886_ = v_suppressElabErrors_899_;
v___y_887_ = v___y_895_;
v___y_888_ = v_ref_903_;
v___y_889_ = v___y_896_;
v___y_890_ = v_val_906_;
goto v___jp_883_;
}
}
v___jp_908_:
{
if (v___y_911_ == 0)
{
v___y_894_ = v___y_909_;
v___y_895_ = v___y_910_;
v___y_896_ = v_severity_812_;
goto v___jp_893_;
}
else
{
v___y_894_ = v___y_909_;
v___y_895_ = v___y_910_;
v___y_896_ = v___x_907_;
goto v___jp_893_;
}
}
v___jp_912_:
{
if (v___y_913_ == 0)
{
uint8_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 1;
v___x_915_ = l_Lean_instBEqMessageSeverity_beq(v_severity_812_, v___x_914_);
if (v___x_915_ == 0)
{
v___y_909_ = v___y_913_;
v___y_910_ = v___y_913_;
v___y_911_ = v___x_915_;
goto v___jp_908_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_816_);
v___x_917_ = l_Lean_warningAsError;
v___x_918_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_916_, v___x_917_);
lean_dec_ref(v___x_916_);
v___y_909_ = v___y_913_;
v___y_910_ = v___y_913_;
v___y_911_ = v___x_918_;
goto v___jp_908_;
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v_msgData_811_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_923_, lean_object* v_msgData_924_, lean_object* v_severity_925_, lean_object* v_isSilent_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v_severity_boxed_932_; uint8_t v_isSilent_boxed_933_; lean_object* v_res_934_; 
v_severity_boxed_932_ = lean_unbox(v_severity_925_);
v_isSilent_boxed_933_ = lean_unbox(v_isSilent_926_);
v_res_934_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_923_, v_msgData_924_, v_severity_boxed_932_, v_isSilent_boxed_933_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_ref_923_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_935_, size_t v_sz_936_, size_t v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_937_, v_sz_936_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_938_);
return v___x_947_;
}
else
{
lean_object* v_ref_948_; lean_object* v_a_949_; uint8_t v_severity_950_; uint8_t v_isSilent_951_; lean_object* v_data_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_ref_948_ = lean_ctor_get(v___y_943_, 2);
v_a_949_ = lean_array_uget_borrowed(v_as_935_, v_i_937_);
v_severity_950_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*5 + 1);
v_isSilent_951_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*5 + 2);
v_data_952_ = lean_ctor_get(v_a_949_, 4);
v___x_953_ = lean_box(0);
lean_inc(v_data_952_);
v___x_954_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_948_, v_data_952_, v_severity_950_, v_isSilent_951_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_954_) == 0)
{
size_t v___x_955_; size_t v___x_956_; 
lean_dec_ref_known(v___x_954_, 1);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_i_937_, v___x_955_);
v_i_937_ = v___x_956_;
v_b_938_ = v___x_953_;
goto _start;
}
else
{
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_970_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_958_, v_sz_boxed_969_, v_i_boxed_970_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_as_958_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_infoState_976_; lean_object* v_env_977_; lean_object* v_nextMacroScope_978_; lean_object* v_ngen_979_; lean_object* v_auxDeclNGen_980_; lean_object* v_traceState_981_; lean_object* v_cache_982_; lean_object* v_recordedDeps_983_; lean_object* v_messages_984_; lean_object* v_snapshotTasks_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1005_; 
v___x_975_ = lean_st_ref_take(v___y_973_);
v_infoState_976_ = lean_ctor_get(v___x_975_, 8);
v_env_977_ = lean_ctor_get(v___x_975_, 0);
v_nextMacroScope_978_ = lean_ctor_get(v___x_975_, 1);
v_ngen_979_ = lean_ctor_get(v___x_975_, 2);
v_auxDeclNGen_980_ = lean_ctor_get(v___x_975_, 3);
v_traceState_981_ = lean_ctor_get(v___x_975_, 4);
v_cache_982_ = lean_ctor_get(v___x_975_, 5);
v_recordedDeps_983_ = lean_ctor_get(v___x_975_, 6);
v_messages_984_ = lean_ctor_get(v___x_975_, 7);
v_snapshotTasks_985_ = lean_ctor_get(v___x_975_, 9);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_987_ = v___x_975_;
v_isShared_988_ = v_isSharedCheck_1005_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snapshotTasks_985_);
lean_inc(v_infoState_976_);
lean_inc(v_messages_984_);
lean_inc(v_recordedDeps_983_);
lean_inc(v_cache_982_);
lean_inc(v_traceState_981_);
lean_inc(v_auxDeclNGen_980_);
lean_inc(v_ngen_979_);
lean_inc(v_nextMacroScope_978_);
lean_inc(v_env_977_);
lean_dec(v___x_975_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1005_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_assignment_989_; lean_object* v_lazyAssignment_990_; lean_object* v_trees_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1004_; 
v_assignment_989_ = lean_ctor_get(v_infoState_976_, 0);
v_lazyAssignment_990_ = lean_ctor_get(v_infoState_976_, 1);
v_trees_991_ = lean_ctor_get(v_infoState_976_, 2);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_infoState_976_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_993_ = v_infoState_976_;
v_isShared_994_ = v_isSharedCheck_1004_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_trees_991_);
lean_inc(v_lazyAssignment_990_);
lean_inc(v_assignment_989_);
lean_dec(v_infoState_976_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1004_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
if (v_isShared_994_ == 0)
{
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_assignment_989_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_lazyAssignment_990_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_trees_991_);
v___x_997_ = v_reuseFailAlloc_1003_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*3, v_flag_972_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 8, v___x_997_);
v___x_999_ = v___x_987_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_env_977_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_nextMacroScope_978_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_ngen_979_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_auxDeclNGen_980_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_traceState_981_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_cache_982_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_recordedDeps_983_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v_messages_984_);
lean_ctor_set(v_reuseFailAlloc_1002_, 8, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1002_, 9, v_snapshotTasks_985_);
v___x_999_ = v_reuseFailAlloc_1002_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_st_ref_put(v___y_973_, v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_995_);
return v___x_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_flag_boxed_1009_; lean_object* v_res_1010_; 
v_flag_boxed_1009_ = lean_unbox(v_flag_1006_);
v_res_1010_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1009_, v___y_1007_);
lean_dec(v___y_1007_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v_infoState_1021_; uint8_t v_enabled_1022_; lean_object* v_a_1024_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1020_ = lean_st_ref_get(v___y_1018_);
v_infoState_1021_ = lean_ctor_get(v___x_1020_, 8);
lean_inc_ref(v_infoState_1021_);
lean_dec(v___x_1020_);
v_enabled_1022_ = lean_ctor_get_uint8(v_infoState_1021_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1021_);
v___x_1034_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1011_, v___y_1018_);
lean_dec_ref(v___x_1034_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
v___x_1035_ = lean_apply_7(v_x_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, lean_box(0));
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1022_, v___y_1018_);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1037_, 0);
lean_dec(v_unused_1045_);
v___x_1039_ = v___x_1037_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v___x_1037_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_a_1036_);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1036_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1046_; 
v_a_1046_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1035_, 1);
v_a_1024_ = v_a_1046_;
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v___x_1025_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1022_, v___y_1018_);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1033_);
v___x_1027_ = v___x_1025_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v___x_1025_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
lean_ctor_set(v___x_1027_, 0, v_a_1024_);
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1024_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_flag_boxed_1056_; lean_object* v_res_1057_; 
v_flag_boxed_1056_ = lean_unbox(v_flag_1047_);
v_res_1057_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1056_, v_x_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1058_, lean_object* v_binders_1059_, lean_object* v_blocks_1060_, lean_object* v_fileMap_x3f_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1067_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1072_; size_t v_sz_1090_; size_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___y_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v_sz_1090_ = lean_array_size(v_blocks_1060_);
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1090_, v___x_1091_, v_blocks_1060_);
v___x_1093_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1093_, 0, v___x_1092_);
v___x_1094_ = 1;
v___x_1095_ = lean_box(v___x_1094_);
v___y_1096_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1096_, 0, v_fileMap_x3f_1061_);
lean_closure_set(v___y_1096_, 1, v_declName_1058_);
lean_closure_set(v___y_1096_, 2, v_binders_1059_);
lean_closure_set(v___y_1096_, 3, v___x_1093_);
lean_closure_set(v___y_1096_, 4, v___x_1095_);
v___x_1097_ = 0;
v___x_1098_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1097_, v___y_1096_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1067_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = l_Lean_Core_setMessageLog___redArg(v_a_1070_, v_a_1067_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; size_t v_sz_1105_; lean_object* v___x_1106_; 
lean_dec_ref_known(v___x_1102_, 1);
v___x_1103_ = l_Lean_MessageLog_toArray(v_a_1101_);
lean_dec(v_a_1101_);
v___x_1104_ = lean_box(0);
v_sz_1105_ = lean_array_size(v___x_1103_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1103_, v_sz_1105_, v___x_1091_, v___x_1104_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec_ref(v___x_1103_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1131_; 
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1106_, 0);
lean_dec(v_unused_1132_);
v___x_1108_ = v___x_1106_;
v_isShared_1109_ = v_isSharedCheck_1131_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v___x_1106_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1131_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1130_; 
v_fst_1110_ = lean_ctor_get(v_a_1099_, 0);
v_snd_1111_ = lean_ctor_get(v_a_1099_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_1099_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1113_ = v_a_1099_;
v_isShared_1114_ = v_isSharedCheck_1130_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_a_1099_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1130_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_fst_1115_; lean_object* v_snd_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1129_; 
v_fst_1115_ = lean_ctor_get(v_fst_1110_, 0);
v_snd_1116_ = lean_ctor_get(v_fst_1110_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_fst_1110_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1118_ = v_fst_1110_;
v_isShared_1119_ = v_isSharedCheck_1129_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_snd_1116_);
lean_inc(v_fst_1115_);
lean_dec(v_fst_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1129_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_fst_1115_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_snd_1116_);
v___x_1121_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1121_);
v___x_1123_ = v___x_1113_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_snd_1111_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1123_);
v___x_1125_ = v___x_1108_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1099_);
v_a_1133_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1106_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1106_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v_a_1141_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1102_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1102_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
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
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1149_; 
lean_dec(v_a_1099_);
v_a_1149_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1100_, 1);
v_a_1072_ = v_a_1149_;
goto v___jp_1071_;
}
}
else
{
lean_object* v_a_1150_; 
v_a_1150_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1098_, 1);
v_a_1072_ = v_a_1150_;
goto v___jp_1071_;
}
v___jp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Core_setMessageLog___redArg(v_a_1070_, v_a_1067_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1081_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 0, v_a_1072_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1072_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_a_1072_);
v_a_1082_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1073_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1073_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_fileMap_x3f_1061_);
lean_dec_ref(v_blocks_1060_);
lean_dec(v_binders_1059_);
lean_dec(v_declName_1058_);
v_a_1151_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1069_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1069_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1159_, lean_object* v_binders_1160_, lean_object* v_blocks_1161_, lean_object* v_fileMap_x3f_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1159_, v_binders_1160_, v_blocks_1161_, v_fileMap_x3f_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1171_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v_flag_boxed_1188_; lean_object* v_res_1189_; 
v_flag_boxed_1188_ = lean_unbox(v_flag_1180_);
v_res_1189_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1188_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1190_, uint8_t v_flag_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_flag_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_flag_boxed_1211_; lean_object* v_res_1212_; 
v_flag_boxed_1211_ = lean_unbox(v_flag_1202_);
v_res_1212_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1201_, v_flag_boxed_1211_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1213_, lean_object* v_msgData_1214_, uint8_t v_severity_1215_, uint8_t v_isSilent_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1213_, v_msgData_1214_, v_severity_1215_, v_isSilent_1216_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1225_, lean_object* v_msgData_1226_, lean_object* v_severity_1227_, lean_object* v_isSilent_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v_severity_boxed_1236_; uint8_t v_isSilent_boxed_1237_; lean_object* v_res_1238_; 
v_severity_boxed_1236_ = lean_unbox(v_severity_1227_);
v_isSilent_boxed_1237_ = lean_unbox(v_isSilent_1228_);
v_res_1238_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1225_, v_msgData_1226_, v_severity_boxed_1236_, v_isSilent_boxed_1237_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v_ref_1225_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1239_, uint8_t v_severity_1240_, uint8_t v_isSilent_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_ref_1247_; lean_object* v___x_1248_; 
v_ref_1247_ = lean_ctor_get(v___y_1244_, 2);
v___x_1248_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1247_, v_msgData_1239_, v_severity_1240_, v_isSilent_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1249_, lean_object* v_severity_1250_, lean_object* v_isSilent_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_severity_boxed_1257_; uint8_t v_isSilent_boxed_1258_; lean_object* v_res_1259_; 
v_severity_boxed_1257_ = lean_unbox(v_severity_1250_);
v_isSilent_boxed_1258_ = lean_unbox(v_isSilent_1251_);
v_res_1259_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1249_, v_severity_boxed_1257_, v_isSilent_boxed_1258_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = 2;
v___x_1269_ = 0;
v___x_1270_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1260_, v___x_1268_, v___x_1269_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1280_, size_t v_sz_1281_, size_t v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_b_1283_);
return v___x_1292_;
}
else
{
lean_object* v_a_1293_; lean_object* v_snd_1294_; lean_object* v_snd_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_a_1293_ = lean_array_uget_borrowed(v_as_1280_, v_i_1282_);
v_snd_1294_ = lean_ctor_get(v_a_1293_, 1);
v_snd_1295_ = lean_ctor_get(v_snd_1294_, 1);
v___x_1296_ = lean_box(0);
lean_inc(v_snd_1295_);
v___x_1297_ = l_Lean_Parser_Error_toString(v_snd_1295_);
v___x_1298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
v___x_1299_ = l_Lean_MessageData_ofFormat(v___x_1298_);
v___x_1300_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1299_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1300_) == 0)
{
size_t v___x_1301_; size_t v___x_1302_; 
lean_dec_ref_known(v___x_1300_, 1);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1282_, v___x_1301_);
v_i_1282_ = v___x_1302_;
v_b_1283_ = v___x_1296_;
goto _start;
}
else
{
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1304_, lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
size_t v_sz_boxed_1315_; size_t v_i_boxed_1316_; lean_object* v_res_1317_; 
v_sz_boxed_1315_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1316_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1304_, v_sz_boxed_1315_, v_i_boxed_1316_, v_b_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v_as_1304_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1336_, lean_object* v_binders_1337_, lean_object* v_docComment_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v_toCold_1347_; lean_object* v_env_1348_; lean_object* v_fileName_1349_; lean_object* v_currNamespace_1350_; lean_object* v_openDecls_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1346_ = lean_st_ref_get(v_a_1344_);
v_toCold_1347_ = lean_ctor_get(v_a_1343_, 0);
v_env_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc_ref_n(v_env_1348_, 2);
lean_dec(v___x_1346_);
v_fileName_1349_ = lean_ctor_get(v_toCold_1347_, 0);
v_currNamespace_1350_ = lean_ctor_get(v_toCold_1347_, 4);
v_openDecls_1351_ = lean_ctor_get(v_toCold_1347_, 5);
v___x_1352_ = lean_string_utf8_byte_size(v_docComment_1338_);
lean_inc_ref_n(v_docComment_1338_, 2);
v___x_1353_ = l_Lean_FileMap_ofString(v_docComment_1338_);
lean_inc_ref(v___x_1353_);
lean_inc_ref(v_fileName_1349_);
v___x_1354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1354_, 0, v_docComment_1338_);
lean_ctor_set(v___x_1354_, 1, v_fileName_1349_);
lean_ctor_set(v___x_1354_, 2, v___x_1353_);
lean_ctor_set(v___x_1354_, 3, v___x_1352_);
v___x_1355_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1343_);
lean_inc(v_openDecls_1351_);
lean_inc(v_currNamespace_1350_);
v___x_1356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1356_, 0, v_env_1348_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_ctor_set(v___x_1356_, 2, v_currNamespace_1350_);
lean_ctor_set(v___x_1356_, 3, v_openDecls_1351_);
v___x_1357_ = l_Lean_Parser_mkParserState(v_docComment_1338_);
lean_dec_ref(v_docComment_1338_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1360_ = l_Lean_Parser_getTokenTable(v_env_1348_);
v___x_1361_ = l_Lean_Parser_ParserFn_run(v___x_1359_, v___x_1354_, v___x_1356_, v___x_1360_, v___x_1357_);
lean_inc_ref(v___x_1361_);
v___x_1362_ = l_Lean_Parser_ParserState_allErrors(v___x_1361_);
v___x_1363_ = lean_array_get_size(v___x_1362_);
v___x_1364_ = lean_nat_dec_eq(v___x_1363_, v___x_1358_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v___x_1361_);
lean_dec_ref(v___x_1353_);
lean_dec(v_binders_1337_);
lean_dec(v_declName_1336_);
v___x_1365_ = lean_box(0);
v_sz_1366_ = lean_array_size(v___x_1362_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1362_, v_sz_1366_, v___x_1367_, v___x_1365_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v___x_1362_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1368_, 0);
lean_dec(v_unused_1377_);
v___x_1370_ = v___x_1368_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v___x_1368_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1368_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1368_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_stxStack_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v___x_1362_);
v_stxStack_1386_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref(v_stxStack_1386_);
lean_dec_ref(v___x_1361_);
v___x_1387_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1386_);
lean_dec_ref(v_stxStack_1386_);
v___x_1388_ = l_Lean_TSyntax_getVersoBlocks(v___x_1387_);
lean_dec(v___x_1387_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1353_);
v___x_1390_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1336_, v_binders_1337_, v___x_1388_, v___x_1389_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1391_, lean_object* v_binders_1392_, lean_object* v_docComment_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_versoDocStringOfText(v_declName_1391_, v_binders_1392_, v_docComment_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1402_, uint8_t v_severity_1403_, uint8_t v_isSilent_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1402_, v_severity_1403_, v_isSilent_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1413_, lean_object* v_severity_1414_, lean_object* v_isSilent_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
uint8_t v_severity_boxed_1423_; uint8_t v_isSilent_boxed_1424_; lean_object* v_res_1425_; 
v_severity_boxed_1423_ = lean_unbox(v_severity_1414_);
v_isSilent_boxed_1424_ = lean_unbox(v_isSilent_1415_);
v_res_1425_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1413_, v_severity_boxed_1423_, v_isSilent_boxed_1424_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1435_, lean_object* v_binders_1436_, lean_object* v_docComment_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1437_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1446_; lean_object* v_body_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
lean_dec_ref_known(v___x_1445_, 1);
v___x_1446_ = lean_unsigned_to_nat(1u);
v_body_1447_ = l_Lean_Syntax_getArg(v_docComment_1437_, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_1449_ = l_Lean_Syntax_isOfKind(v_body_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = l_Lean_TSyntax_getDocString(v_docComment_1437_);
v___x_1451_ = l_Lean_versoDocStringOfText(v_declName_1435_, v_binders_1436_, v___x_1450_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; lean_object* v_markup_1453_; 
v___x_1452_ = l_Lean_VersoDocstringView_of(v_docComment_1437_);
v_markup_1453_ = lean_ctor_get(v___x_1452_, 1);
lean_inc_ref(v_markup_1453_);
lean_dec_ref(v___x_1452_);
if (lean_obj_tag(v_markup_1453_) == 0)
{
lean_object* v_doc_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_doc_1454_ = lean_ctor_get(v_markup_1453_, 0);
lean_inc(v_doc_1454_);
lean_dec_ref_known(v_markup_1453_, 1);
v___x_1455_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1454_);
lean_dec(v_doc_1454_);
v___x_1456_ = lean_box(0);
v___x_1457_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1435_, v_binders_1436_, v___x_1455_, v___x_1456_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
return v___x_1457_;
}
else
{
lean_object* v_text_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_text_1458_ = lean_ctor_get(v_markup_1453_, 0);
lean_inc(v_text_1458_);
lean_dec_ref_known(v_markup_1453_, 1);
v___x_1459_ = l_Lean_Syntax_getAtomVal(v_text_1458_);
lean_dec(v_text_1458_);
v___x_1460_ = l_Lean_versoDocStringOfText(v_declName_1435_, v_binders_1436_, v___x_1459_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
return v___x_1460_;
}
}
}
else
{
lean_object* v___x_1461_; 
lean_dec_ref_known(v___x_1445_, 1);
v___x_1461_ = l_Lean_parseVersoDocString(v_docComment_1437_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1509_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1509_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1509_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
if (lean_obj_tag(v_a_1462_) == 1)
{
lean_object* v_val_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; 
lean_del_object(v___x_1464_);
v_val_1466_ = lean_ctor_get(v_a_1462_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_a_1462_, 1);
v___x_1467_ = l_Lean_TSyntax_getVersoBlocks(v_val_1466_);
lean_dec(v_val_1466_);
v___x_1468_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1468_, 0, v___x_1467_);
v___x_1469_ = 0;
v___x_1470_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1435_, v_binders_1436_, v___x_1468_, v___x_1469_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1496_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1496_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1496_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1495_; 
v_fst_1475_ = lean_ctor_get(v_a_1471_, 0);
v_snd_1476_ = lean_ctor_get(v_a_1471_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1478_ = v_a_1471_;
v_isShared_1479_ = v_isSharedCheck_1495_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_snd_1476_);
lean_inc(v_fst_1475_);
lean_dec(v_a_1471_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1495_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1494_; 
v_fst_1480_ = lean_ctor_get(v_fst_1475_, 0);
v_snd_1481_ = lean_ctor_get(v_fst_1475_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_fst_1475_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1483_ = v_fst_1475_;
v_isShared_1484_ = v_isSharedCheck_1494_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snd_1481_);
lean_inc(v_fst_1480_);
lean_dec(v_fst_1475_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1494_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_fst_1480_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_snd_1481_);
v___x_1486_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1486_);
v___x_1488_ = v___x_1478_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1476_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1488_);
v___x_1490_ = v___x_1473_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
v_a_1497_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1470_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1470_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
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
lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_dec(v_a_1462_);
lean_dec(v_binders_1436_);
lean_dec(v_declName_1435_);
v___x_1505_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1505_);
v___x_1507_ = v___x_1464_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_binders_1436_);
lean_dec(v_declName_1435_);
v_a_1510_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1461_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1461_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1518_, lean_object* v_binders_1519_, lean_object* v_docComment_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_versoDocString(v_declName_1518_, v_binders_1519_, v_docComment_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_docComment_1520_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1529_, lean_object* v_doc_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v_val_1546_; lean_object* v_env_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1538_ = lean_st_ref_get(v_a_1536_);
v_env_1548_ = lean_ctor_get(v___x_1538_, 0);
lean_inc_ref(v_env_1548_);
lean_dec(v___x_1538_);
v___x_1549_ = l_Lean_getMainVersoModuleDocs(v_env_1548_);
v___x_1550_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1549_);
lean_dec_ref(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1530_);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___y_1540_ = v___x_1551_;
v___y_1541_ = v___x_1552_;
goto v___jp_1539_;
}
else
{
lean_object* v_val_1553_; 
v_val_1553_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1550_, 1);
v_val_1546_ = v_val_1553_;
goto v___jp_1545_;
}
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_val_1554_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_val_1554_, v___x_1555_);
lean_dec(v_val_1554_);
v_val_1546_ = v___x_1556_;
goto v___jp_1545_;
}
v___jp_1539_:
{
lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1542_, 0, v_range_1529_);
lean_closure_set(v___x_1542_, 1, v___y_1540_);
lean_closure_set(v___x_1542_, 2, v___y_1541_);
v___x_1543_ = 0;
v___x_1544_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1542_, v___x_1543_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
return v___x_1544_;
}
v___jp_1545_:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1530_);
v___y_1540_ = v___x_1547_;
v___y_1541_ = v_val_1546_;
goto v___jp_1539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1557_, lean_object* v_doc_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_versoModDocString(v_range_1557_, v_doc_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_doc_1558_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1576_, lean_object* v_docComment_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1586_ = l_Lean_versoDocStringOfText(v_declName_1576_, v___x_1585_, v_docComment_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1587_, lean_object* v_docComment_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_versoDocStringFromString(v_declName_1587_, v_docComment_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1597_, lean_object* v_declName_1598_, uint8_t v___x_1599_, lean_object* v_env_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = l_Lean_docStringExt;
v___x_1602_ = l_String_removeLeadingSpaces(v_docString_1597_);
v___x_1603_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1601_, v_env_1600_, v_declName_1598_, v___x_1602_, v___x_1599_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0___boxed(lean_object* v_docString_1604_, lean_object* v_declName_1605_, lean_object* v___x_1606_, lean_object* v_env_1607_){
_start:
{
uint8_t v___x_183__boxed_1608_; lean_object* v_res_1609_; 
v___x_183__boxed_1608_ = lean_unbox(v___x_1606_);
v_res_1609_ = l_Lean_addMarkdownDocString___redArg___lam__0(v_docString_1604_, v_declName_1605_, v___x_183__boxed_1608_, v_env_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1610_, uint8_t v___x_1611_, lean_object* v_modifyEnv_1612_, lean_object* v_docString_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_box(v___x_1611_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1615_, 0, v_docString_1613_);
lean_closure_set(v___f_1615_, 1, v_declName_1610_);
lean_closure_set(v___f_1615_, 2, v___x_1614_);
v___x_1616_ = lean_apply_1(v_modifyEnv_1612_, v___f_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1___boxed(lean_object* v_declName_1617_, lean_object* v___x_1618_, lean_object* v_modifyEnv_1619_, lean_object* v_docString_1620_){
_start:
{
uint8_t v___x_192__boxed_1621_; lean_object* v_res_1622_; 
v___x_192__boxed_1621_ = lean_unbox(v___x_1618_);
v_res_1622_ = l_Lean_addMarkdownDocString___redArg___lam__1(v_declName_1617_, v___x_192__boxed_1621_, v_modifyEnv_1619_, v_docString_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_docComment_1625_, lean_object* v_toBind_1626_, lean_object* v___f_1627_, lean_object* v_____r_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = l_Lean_getDocStringText___redArg(v_inst_1623_, v_inst_1624_, v_docComment_1625_);
v___x_1630_ = lean_apply_4(v_toBind_1626_, lean_box(0), lean_box(0), v___x_1629_, v___f_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_docComment_1636_, lean_object* v_toBind_1637_, lean_object* v___f_1638_, lean_object* v_____r_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = l_Lean_validateDocComment___redArg(v_inst_1631_, v_inst_1632_, v_inst_1633_, v_inst_1634_, v_inst_1635_, v_docComment_1636_);
v___x_1641_ = lean_apply_4(v_toBind_1637_, lean_box(0), lean_box(0), v___x_1640_, v___f_1638_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_docComment_1647_, lean_object* v_toBind_1648_, lean_object* v___f_1649_, lean_object* v_____r_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_, v_docComment_1647_, v_toBind_1648_, v___f_1649_, v_____r_1650_);
lean_dec(v_docComment_1647_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1652_, lean_object* v_____r_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_apply_1(v___f_1652_, v_____r_1653_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_1661_, lean_object* v_declName_1662_, uint8_t v___x_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_toBind_1666_, lean_object* v___f_1667_, lean_object* v_____do__lift_1668_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1668_, v_declName_1662_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_dec(v___f_1667_);
lean_dec(v_toBind_1666_);
lean_dec_ref(v_inst_1665_);
lean_dec_ref(v_inst_1664_);
lean_dec(v_declName_1662_);
goto v___jp_1669_;
}
else
{
lean_dec_ref_known(v___x_1672_, 1);
if (v___x_1663_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___f_1661_);
v___x_1673_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1674_ = l_Lean_MessageData_ofConstName(v_declName_1662_, v___x_1663_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_throwError___redArg(v_inst_1664_, v_inst_1665_, v___x_1677_);
v___x_1679_ = lean_apply_4(v_toBind_1666_, lean_box(0), lean_box(0), v___x_1678_, v___f_1667_);
return v___x_1679_;
}
else
{
lean_dec(v___f_1667_);
lean_dec(v_toBind_1666_);
lean_dec_ref(v_inst_1665_);
lean_dec_ref(v_inst_1664_);
lean_dec(v_declName_1662_);
goto v___jp_1669_;
}
}
v___jp_1669_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_apply_1(v___f_1661_, v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_1680_, lean_object* v_declName_1681_, lean_object* v___x_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_toBind_1685_, lean_object* v___f_1686_, lean_object* v_____do__lift_1687_){
_start:
{
uint8_t v___x_257__boxed_1688_; lean_object* v_res_1689_; 
v___x_257__boxed_1688_ = lean_unbox(v___x_1682_);
v_res_1689_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_1680_, v_declName_1681_, v___x_257__boxed_1688_, v_inst_1683_, v_inst_1684_, v_toBind_1685_, v___f_1686_, v_____do__lift_1687_);
lean_dec_ref(v_____do__lift_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_declName_1697_, lean_object* v_docComment_1698_){
_start:
{
lean_object* v_toApplicative_1699_; lean_object* v_toBind_1700_; lean_object* v_toPure_1701_; uint8_t v___x_1702_; 
v_toApplicative_1699_ = lean_ctor_get(v_inst_1690_, 0);
v_toBind_1700_ = lean_ctor_get(v_inst_1690_, 1);
lean_inc(v_toBind_1700_);
v_toPure_1701_ = lean_ctor_get(v_toApplicative_1699_, 1);
v___x_1702_ = l_Lean_Name_isAnonymous(v_declName_1697_);
if (v___x_1702_ == 0)
{
lean_object* v_getEnv_1703_; lean_object* v_modifyEnv_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; 
v_getEnv_1703_ = lean_ctor_get(v_inst_1693_, 0);
lean_inc(v_getEnv_1703_);
v_modifyEnv_1704_ = lean_ctor_get(v_inst_1693_, 1);
lean_inc(v_modifyEnv_1704_);
lean_dec_ref(v_inst_1693_);
v___x_1705_ = 1;
v___x_1706_ = lean_box(v___x_1705_);
lean_inc(v_declName_1697_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1707_, 0, v_declName_1697_);
lean_closure_set(v___f_1707_, 1, v___x_1706_);
lean_closure_set(v___f_1707_, 2, v_modifyEnv_1704_);
lean_inc_n(v_toBind_1700_, 3);
lean_inc(v_docComment_1698_);
lean_inc_ref(v_inst_1694_);
lean_inc_ref_n(v_inst_1690_, 2);
v___f_1708_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1708_, 0, v_inst_1690_);
lean_closure_set(v___f_1708_, 1, v_inst_1694_);
lean_closure_set(v___f_1708_, 2, v_docComment_1698_);
lean_closure_set(v___f_1708_, 3, v_toBind_1700_);
lean_closure_set(v___f_1708_, 4, v___f_1707_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1709_, 0, v_inst_1690_);
lean_closure_set(v___f_1709_, 1, v_inst_1691_);
lean_closure_set(v___f_1709_, 2, v_inst_1695_);
lean_closure_set(v___f_1709_, 3, v_inst_1696_);
lean_closure_set(v___f_1709_, 4, v_inst_1692_);
lean_closure_set(v___f_1709_, 5, v_docComment_1698_);
lean_closure_set(v___f_1709_, 6, v_toBind_1700_);
lean_closure_set(v___f_1709_, 7, v___f_1708_);
lean_inc_ref(v___f_1709_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1710_, 0, v___f_1709_);
v___x_1711_ = lean_box(v___x_1702_);
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1712_, 0, v___f_1709_);
lean_closure_set(v___f_1712_, 1, v_declName_1697_);
lean_closure_set(v___f_1712_, 2, v___x_1711_);
lean_closure_set(v___f_1712_, 3, v_inst_1690_);
lean_closure_set(v___f_1712_, 4, v_inst_1694_);
lean_closure_set(v___f_1712_, 5, v_toBind_1700_);
lean_closure_set(v___f_1712_, 6, v___f_1710_);
v___x_1713_ = lean_apply_4(v_toBind_1700_, lean_box(0), lean_box(0), v_getEnv_1703_, v___f_1712_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_inc(v_toPure_1701_);
lean_dec(v_toBind_1700_);
lean_dec(v_docComment_1698_);
lean_dec(v_declName_1697_);
lean_dec(v_inst_1696_);
lean_dec_ref(v_inst_1695_);
lean_dec_ref(v_inst_1694_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
lean_dec(v_inst_1691_);
lean_dec_ref(v_inst_1690_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_apply_2(v_toPure_1701_, lean_box(0), v___x_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_declName_1724_, lean_object* v_docComment_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_addMarkdownDocString___redArg(v_inst_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_declName_1724_, v_docComment_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_s_1729_){
_start:
{
lean_object* v_addEntryFn_1730_; lean_object* v_importedEntries_1731_; lean_object* v_state_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_addEntryFn_1730_ = lean_ctor_get(v___x_1727_, 3);
lean_inc(v_addEntryFn_1730_);
lean_dec_ref(v___x_1727_);
v_importedEntries_1731_ = lean_ctor_get(v_s_1729_, 0);
v_state_1732_ = lean_ctor_get(v_s_1729_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_s_1729_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v_s_1729_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_state_1732_);
lean_inc(v_importedEntries_1731_);
lean_dec(v_s_1729_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_state_1736_; lean_object* v___x_1738_; 
v_state_1736_ = lean_apply_2(v_addEntryFn_1730_, v_state_1732_, v___x_1728_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_state_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_importedEntries_1731_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_state_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1741_, lean_object* v_x1_1742_, lean_object* v_x2_1743_){
_start:
{
lean_object* v_index_1744_; lean_object* v_sourceString_1745_; lean_object* v_imports_1746_; lean_object* v_currNamespace_1747_; lean_object* v_openDecls_1748_; lean_object* v_options_1749_; lean_object* v_check_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1768_; 
v_index_1744_ = lean_ctor_get(v_x2_1743_, 1);
v_sourceString_1745_ = lean_ctor_get(v_x2_1743_, 2);
v_imports_1746_ = lean_ctor_get(v_x2_1743_, 3);
v_currNamespace_1747_ = lean_ctor_get(v_x2_1743_, 4);
v_openDecls_1748_ = lean_ctor_get(v_x2_1743_, 5);
v_options_1749_ = lean_ctor_get(v_x2_1743_, 6);
v_check_1750_ = lean_ctor_get(v_x2_1743_, 7);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x2_1743_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_x2_1743_, 0);
lean_dec(v_unused_1769_);
v___x_1752_ = v_x2_1743_;
v_isShared_1753_ = v_isSharedCheck_1768_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_check_1750_);
lean_inc(v_options_1749_);
lean_inc(v_openDecls_1748_);
lean_inc(v_currNamespace_1747_);
lean_inc(v_imports_1746_);
lean_inc(v_sourceString_1745_);
lean_inc(v_index_1744_);
lean_dec(v_x2_1743_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1768_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v_toEnvExtension_1755_; lean_object* v_asyncMode_1756_; uint8_t v_logWrites_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1754_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1755_ = lean_ctor_get(v___x_1754_, 0);
v_asyncMode_1756_ = lean_ctor_get(v_toEnvExtension_1755_, 2);
v_logWrites_1757_ = lean_ctor_get_uint8(v_toEnvExtension_1755_, sizeof(void*)*6);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_declName_1741_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1758_);
v___x_1760_ = v___x_1752_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_index_1744_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_sourceString_1745_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_imports_1746_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_currNamespace_1747_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v_openDecls_1748_);
lean_ctor_set(v_reuseFailAlloc_1767_, 6, v_options_1749_);
lean_ctor_set(v_reuseFailAlloc_1767_, 7, v_check_1750_);
v___x_1760_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___f_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1761_, 0, v___x_1754_);
lean_closure_set(v___f_1761_, 1, v___x_1760_);
v___x_1762_ = lean_box(0);
v___x_1763_ = 1;
if (v_logWrites_1757_ == 0)
{
lean_object* v___x_1764_; 
lean_inc_ref(v_toEnvExtension_1755_);
v___x_1764_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1755_, v_x1_1742_, v___f_1761_, v_asyncMode_1756_, v___x_1762_, v___x_1763_);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_inc_ref_n(v_toEnvExtension_1755_, 2);
v___x_1765_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1755_, v_x1_1742_);
lean_dec_ref(v_x1_1742_);
v___x_1766_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1755_, v___x_1765_, v___f_1761_, v_asyncMode_1756_, v___x_1762_, v___x_1763_);
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_1789_, lean_object* v_docs_1790_, uint8_t v___x_1791_, lean_object* v_deferred_1792_, lean_object* v___f_1793_, lean_object* v_env_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v_env_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1795_ = l_Lean_versoDocStringExt;
v_env_1796_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1795_, v_env_1794_, v_declName_1789_, v_docs_1790_, v___x_1791_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_array_get_size(v_deferred_1792_);
v___x_1799_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1800_ = lean_nat_dec_lt(v___x_1797_, v___x_1798_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v___f_1793_);
lean_dec_ref(v_deferred_1792_);
return v_env_1796_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_nat_dec_le(v___x_1798_, v___x_1798_);
if (v___x_1801_ == 0)
{
if (v___x_1800_ == 0)
{
lean_dec_ref(v___f_1793_);
lean_dec_ref(v_deferred_1792_);
return v_env_1796_;
}
else
{
size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = lean_usize_of_nat(v___x_1798_);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1799_, v___f_1793_, v_deferred_1792_, v___x_1802_, v___x_1803_, v_env_1796_);
return v___x_1804_;
}
}
else
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = lean_usize_of_nat(v___x_1798_);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1799_, v___f_1793_, v_deferred_1792_, v___x_1805_, v___x_1806_, v_env_1796_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1808_, lean_object* v_docs_1809_, lean_object* v___x_1810_, lean_object* v_deferred_1811_, lean_object* v___f_1812_, lean_object* v_env_1813_){
_start:
{
uint8_t v___x_379__boxed_1814_; lean_object* v_res_1815_; 
v___x_379__boxed_1814_ = lean_unbox(v___x_1810_);
v_res_1815_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_1808_, v_docs_1809_, v___x_379__boxed_1814_, v_deferred_1811_, v___f_1812_, v_env_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_modifyEnv_1816_, lean_object* v___f_1817_, lean_object* v_____r_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_apply_1(v_modifyEnv_1816_, v___f_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object* v_declName_1822_, lean_object* v_modifyEnv_1823_, lean_object* v___f_1824_, uint8_t v___x_1825_, uint8_t v___x_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_toBind_1829_, lean_object* v___f_1830_, lean_object* v_____do__lift_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1831_, v_declName_1822_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; 
lean_dec(v___f_1830_);
lean_dec(v_toBind_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec(v_declName_1822_);
v___x_1833_ = lean_apply_1(v_modifyEnv_1823_, v___f_1824_);
return v___x_1833_;
}
else
{
lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1849_; 
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v___x_1832_, 0);
lean_dec(v_unused_1850_);
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
else
{
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
if (v___x_1825_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v___f_1824_);
lean_dec(v_modifyEnv_1823_);
v___x_1837_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_1838_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1822_, v___x_1826_);
v___x_1839_ = lean_string_append(v___x_1837_, v___x_1838_);
lean_dec_ref(v___x_1838_);
v___x_1840_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_1841_ = lean_string_append(v___x_1839_, v___x_1840_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 3);
lean_ctor_set(v___x_1835_, 0, v___x_1841_);
v___x_1843_ = v___x_1835_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = l_Lean_MessageData_ofFormat(v___x_1843_);
v___x_1845_ = l_Lean_throwError___redArg(v_inst_1827_, v_inst_1828_, v___x_1844_);
v___x_1846_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v___x_1845_, v___f_1830_);
return v___x_1846_;
}
}
else
{
lean_object* v___x_1848_; 
lean_del_object(v___x_1835_);
lean_dec(v___f_1830_);
lean_dec(v_toBind_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec(v_declName_1822_);
v___x_1848_ = lean_apply_1(v_modifyEnv_1823_, v___f_1824_);
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object* v_declName_1851_, lean_object* v_modifyEnv_1852_, lean_object* v___f_1853_, lean_object* v___x_1854_, lean_object* v___x_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_toBind_1858_, lean_object* v___f_1859_, lean_object* v_____do__lift_1860_){
_start:
{
uint8_t v___x_439__boxed_1861_; uint8_t v___x_440__boxed_1862_; lean_object* v_res_1863_; 
v___x_439__boxed_1861_ = lean_unbox(v___x_1854_);
v___x_440__boxed_1862_ = lean_unbox(v___x_1855_);
v_res_1863_ = l_Lean_addVersoDocStringCore___redArg___lam__4(v_declName_1851_, v_modifyEnv_1852_, v___f_1853_, v___x_439__boxed_1861_, v___x_440__boxed_1862_, v_inst_1856_, v_inst_1857_, v_toBind_1858_, v___f_1859_, v_____do__lift_1860_);
lean_dec_ref(v_____do__lift_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_declName_1867_, lean_object* v_docs_1868_, lean_object* v_deferred_1869_){
_start:
{
lean_object* v_toApplicative_1870_; lean_object* v_toBind_1871_; lean_object* v_toPure_1872_; uint8_t v___x_1873_; 
v_toApplicative_1870_ = lean_ctor_get(v_inst_1864_, 0);
v_toBind_1871_ = lean_ctor_get(v_inst_1864_, 1);
lean_inc(v_toBind_1871_);
v_toPure_1872_ = lean_ctor_get(v_toApplicative_1870_, 1);
v___x_1873_ = l_Lean_Name_isAnonymous(v_declName_1867_);
if (v___x_1873_ == 0)
{
lean_object* v_getEnv_1874_; lean_object* v_modifyEnv_1875_; lean_object* v___f_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v_getEnv_1874_ = lean_ctor_get(v_inst_1865_, 0);
lean_inc(v_getEnv_1874_);
v_modifyEnv_1875_ = lean_ctor_get(v_inst_1865_, 1);
lean_inc_n(v_modifyEnv_1875_, 2);
lean_dec_ref(v_inst_1865_);
lean_inc_n(v_declName_1867_, 2);
v___f_1876_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1876_, 0, v_declName_1867_);
v___x_1877_ = 1;
v___x_1878_ = lean_box(v___x_1877_);
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1879_, 0, v_declName_1867_);
lean_closure_set(v___f_1879_, 1, v_docs_1868_);
lean_closure_set(v___f_1879_, 2, v___x_1878_);
lean_closure_set(v___f_1879_, 3, v_deferred_1869_);
lean_closure_set(v___f_1879_, 4, v___f_1876_);
lean_inc_ref(v___f_1879_);
v___f_1880_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3), 3, 2);
lean_closure_set(v___f_1880_, 0, v_modifyEnv_1875_);
lean_closure_set(v___f_1880_, 1, v___f_1879_);
v___x_1881_ = lean_box(v___x_1873_);
v___x_1882_ = lean_box(v___x_1877_);
lean_inc(v_toBind_1871_);
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1883_, 0, v_declName_1867_);
lean_closure_set(v___f_1883_, 1, v_modifyEnv_1875_);
lean_closure_set(v___f_1883_, 2, v___f_1879_);
lean_closure_set(v___f_1883_, 3, v___x_1881_);
lean_closure_set(v___f_1883_, 4, v___x_1882_);
lean_closure_set(v___f_1883_, 5, v_inst_1864_);
lean_closure_set(v___f_1883_, 6, v_inst_1866_);
lean_closure_set(v___f_1883_, 7, v_toBind_1871_);
lean_closure_set(v___f_1883_, 8, v___f_1880_);
v___x_1884_ = lean_apply_4(v_toBind_1871_, lean_box(0), lean_box(0), v_getEnv_1874_, v___f_1883_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_inc(v_toPure_1872_);
lean_dec(v_toBind_1871_);
lean_dec_ref(v_deferred_1869_);
lean_dec_ref(v_docs_1868_);
lean_dec(v_declName_1867_);
lean_dec_ref(v_inst_1866_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_apply_2(v_toPure_1872_, lean_box(0), v___x_1885_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_declName_1892_, lean_object* v_docs_1893_, lean_object* v_deferred_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1888_, v_inst_1889_, v_inst_1891_, v_declName_1892_, v_docs_1893_, v_deferred_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_declName_1901_, lean_object* v_docs_1902_, lean_object* v_deferred_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_addVersoDocStringCore(v_m_1896_, v_inst_1897_, v_inst_1898_, v_inst_1899_, v_inst_1900_, v_declName_1901_, v_docs_1902_, v_deferred_1903_);
lean_dec(v_inst_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_size_1905_, uint8_t v___x_1906_, lean_object* v_x1_1907_, lean_object* v_x2_1908_){
_start:
{
lean_object* v_index_1909_; lean_object* v_sourceString_1910_; lean_object* v_imports_1911_; lean_object* v_currNamespace_1912_; lean_object* v_openDecls_1913_; lean_object* v_options_1914_; lean_object* v_check_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1932_; 
v_index_1909_ = lean_ctor_get(v_x2_1908_, 1);
v_sourceString_1910_ = lean_ctor_get(v_x2_1908_, 2);
v_imports_1911_ = lean_ctor_get(v_x2_1908_, 3);
v_currNamespace_1912_ = lean_ctor_get(v_x2_1908_, 4);
v_openDecls_1913_ = lean_ctor_get(v_x2_1908_, 5);
v_options_1914_ = lean_ctor_get(v_x2_1908_, 6);
v_check_1915_ = lean_ctor_get(v_x2_1908_, 7);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x2_1908_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_x2_1908_, 0);
lean_dec(v_unused_1933_);
v___x_1917_ = v_x2_1908_;
v_isShared_1918_ = v_isSharedCheck_1932_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_check_1915_);
lean_inc(v_options_1914_);
lean_inc(v_openDecls_1913_);
lean_inc(v_currNamespace_1912_);
lean_inc(v_imports_1911_);
lean_inc(v_sourceString_1910_);
lean_inc(v_index_1909_);
lean_dec(v_x2_1908_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1932_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v_toEnvExtension_1920_; lean_object* v_asyncMode_1921_; uint8_t v_logWrites_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1919_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1920_ = lean_ctor_get(v___x_1919_, 0);
v_asyncMode_1921_ = lean_ctor_get(v_toEnvExtension_1920_, 2);
v_logWrites_1922_ = lean_ctor_get_uint8(v_toEnvExtension_1920_, sizeof(void*)*6);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_size_1905_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1923_);
v___x_1925_ = v___x_1917_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_index_1909_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_sourceString_1910_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_imports_1911_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_currNamespace_1912_);
lean_ctor_set(v_reuseFailAlloc_1931_, 5, v_openDecls_1913_);
lean_ctor_set(v_reuseFailAlloc_1931_, 6, v_options_1914_);
lean_ctor_set(v_reuseFailAlloc_1931_, 7, v_check_1915_);
v___x_1925_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___f_1926_; lean_object* v___x_1927_; 
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1926_, 0, v___x_1919_);
lean_closure_set(v___f_1926_, 1, v___x_1925_);
v___x_1927_ = lean_box(0);
if (v_logWrites_1922_ == 0)
{
lean_object* v___x_1928_; 
lean_inc_ref(v_toEnvExtension_1920_);
v___x_1928_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1920_, v_x1_1907_, v___f_1926_, v_asyncMode_1921_, v___x_1927_, v___x_1906_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_inc_ref_n(v_toEnvExtension_1920_, 2);
v___x_1929_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1920_, v_x1_1907_);
lean_dec_ref(v_x1_1907_);
v___x_1930_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1920_, v___x_1929_, v___f_1926_, v_asyncMode_1921_, v___x_1927_, v___x_1906_);
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed(lean_object* v_size_1934_, lean_object* v___x_1935_, lean_object* v_x1_1936_, lean_object* v_x2_1937_){
_start:
{
uint8_t v___x_313__boxed_1938_; lean_object* v_res_1939_; 
v___x_313__boxed_1938_ = lean_unbox(v___x_1935_);
v_res_1939_ = l_Lean_addVersoModDocStringCore___redArg___lam__1(v_size_1934_, v___x_313__boxed_1938_, v_x1_1936_, v_x2_1937_);
return v_res_1939_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_deferred_1946_, lean_object* v_inst_1947_, lean_object* v___f_1948_, lean_object* v_____do__lift_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1949_, v_docs_1943_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec_ref(v___f_1948_);
lean_dec_ref(v_inst_1947_);
lean_dec_ref(v_deferred_1946_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_1953_ = l_Lean_stringToMessageData(v_a_1951_);
v___x_1954_ = l_Lean_indentD(v___x_1953_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1952_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_throwError___redArg(v_inst_1944_, v_inst_1945_, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
lean_dec_ref(v_inst_1945_);
lean_dec_ref(v_inst_1944_);
v_a_1957_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_array_get_size(v_deferred_1946_);
v___x_1960_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1961_ = lean_nat_dec_lt(v___x_1958_, v___x_1959_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref(v___f_1948_);
lean_dec_ref(v_deferred_1946_);
v___x_1962_ = l_Lean_setEnv___redArg(v_inst_1947_, v_a_1957_);
return v___x_1962_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_nat_dec_le(v___x_1959_, v___x_1959_);
if (v___x_1963_ == 0)
{
if (v___x_1961_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v___f_1948_);
lean_dec_ref(v_deferred_1946_);
v___x_1964_ = l_Lean_setEnv___redArg(v_inst_1947_, v_a_1957_);
return v___x_1964_;
}
else
{
size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = lean_usize_of_nat(v___x_1959_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1960_, v___f_1948_, v_deferred_1946_, v___x_1965_, v___x_1966_, v_a_1957_);
v___x_1968_ = l_Lean_setEnv___redArg(v_inst_1947_, v___x_1967_);
return v___x_1968_;
}
}
else
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1959_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1960_, v___f_1948_, v_deferred_1946_, v___x_1969_, v___x_1970_, v_a_1957_);
v___x_1972_ = l_Lean_setEnv___redArg(v_inst_1947_, v___x_1971_);
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(uint8_t v___x_1973_, lean_object* v_docs_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_deferred_1977_, lean_object* v_inst_1978_, lean_object* v_toBind_1979_, lean_object* v_getEnv_1980_, lean_object* v_____do__lift_1981_){
_start:
{
lean_object* v___x_1982_; lean_object* v_size_1983_; lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; 
v___x_1982_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_1981_);
v_size_1983_ = lean_ctor_get(v___x_1982_, 2);
lean_inc(v_size_1983_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = lean_box(v___x_1973_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1985_, 0, v_size_1983_);
lean_closure_set(v___f_1985_, 1, v___x_1984_);
v___f_1986_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1986_, 0, v_docs_1974_);
lean_closure_set(v___f_1986_, 1, v_inst_1975_);
lean_closure_set(v___f_1986_, 2, v_inst_1976_);
lean_closure_set(v___f_1986_, 3, v_deferred_1977_);
lean_closure_set(v___f_1986_, 4, v_inst_1978_);
lean_closure_set(v___f_1986_, 5, v___f_1985_);
v___x_1987_ = lean_apply_4(v_toBind_1979_, lean_box(0), lean_box(0), v_getEnv_1980_, v___f_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed(lean_object* v___x_1988_, lean_object* v_docs_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_deferred_1992_, lean_object* v_inst_1993_, lean_object* v_toBind_1994_, lean_object* v_getEnv_1995_, lean_object* v_____do__lift_1996_){
_start:
{
uint8_t v___x_436__boxed_1997_; lean_object* v_res_1998_; 
v___x_436__boxed_1997_ = lean_unbox(v___x_1988_);
v_res_1998_ = l_Lean_addVersoModDocStringCore___redArg___lam__2(v___x_436__boxed_1997_, v_docs_1989_, v_inst_1990_, v_inst_1991_, v_deferred_1992_, v_inst_1993_, v_toBind_1994_, v_getEnv_1995_, v_____do__lift_1996_);
return v_res_1998_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_docs_2004_, lean_object* v_deferred_2005_, lean_object* v_inst_2006_, lean_object* v_toBind_2007_, lean_object* v_getEnv_2008_, lean_object* v_____do__lift_2009_){
_start:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = l_Lean_getMainModuleDoc(v_____do__lift_2009_);
v___x_2011_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2010_);
lean_dec_ref(v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_getEnv_2008_);
lean_dec(v_toBind_2007_);
lean_dec_ref(v_inst_2006_);
lean_dec_ref(v_deferred_2005_);
lean_dec_ref(v_docs_2004_);
v___x_2012_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2013_ = l_Lean_throwError___redArg(v_inst_2002_, v_inst_2003_, v___x_2012_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(v___x_2011_);
lean_inc(v_getEnv_2008_);
lean_inc(v_toBind_2007_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2015_, 0, v___x_2014_);
lean_closure_set(v___f_2015_, 1, v_docs_2004_);
lean_closure_set(v___f_2015_, 2, v_inst_2002_);
lean_closure_set(v___f_2015_, 3, v_inst_2003_);
lean_closure_set(v___f_2015_, 4, v_deferred_2005_);
lean_closure_set(v___f_2015_, 5, v_inst_2006_);
lean_closure_set(v___f_2015_, 6, v_toBind_2007_);
lean_closure_set(v___f_2015_, 7, v_getEnv_2008_);
v___x_2016_ = lean_apply_4(v_toBind_2007_, lean_box(0), lean_box(0), v_getEnv_2008_, v___f_2015_);
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_docs_2020_, lean_object* v_deferred_2021_){
_start:
{
lean_object* v_toBind_2022_; lean_object* v_getEnv_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; 
v_toBind_2022_ = lean_ctor_get(v_inst_2017_, 1);
lean_inc_n(v_toBind_2022_, 2);
v_getEnv_2023_ = lean_ctor_get(v_inst_2018_, 0);
lean_inc_n(v_getEnv_2023_, 2);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2024_, 0, v_inst_2017_);
lean_closure_set(v___f_2024_, 1, v_inst_2019_);
lean_closure_set(v___f_2024_, 2, v_docs_2020_);
lean_closure_set(v___f_2024_, 3, v_deferred_2021_);
lean_closure_set(v___f_2024_, 4, v_inst_2018_);
lean_closure_set(v___f_2024_, 5, v_toBind_2022_);
lean_closure_set(v___f_2024_, 6, v_getEnv_2023_);
v___x_2025_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v_getEnv_2023_, v___f_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_docs_2031_, lean_object* v_deferred_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2027_, v_inst_2028_, v_inst_2030_, v_docs_2031_, v_deferred_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_docs_2039_, lean_object* v_deferred_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_addVersoModDocStringCore(v_m_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v_inst_2038_, v_docs_2039_, v_deferred_2040_);
lean_dec(v_inst_2037_);
return v_res_2041_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_box(1);
v___x_2043_ = l_Lean_MessageData_ofFormat(v___x_2042_);
return v___x_2043_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2));
v___x_2048_ = l_Lean_MessageData_ofFormat(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(lean_object* v_x_2049_, lean_object* v_x_2050_){
_start:
{
if (lean_obj_tag(v_x_2050_) == 0)
{
return v_x_2049_;
}
else
{
lean_object* v_head_2051_; lean_object* v_tail_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2074_; 
v_head_2051_ = lean_ctor_get(v_x_2050_, 0);
v_tail_2052_ = lean_ctor_get(v_x_2050_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_x_2050_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2054_ = v_x_2050_;
v_isShared_2055_ = v_isSharedCheck_2074_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_tail_2052_);
lean_inc(v_head_2051_);
lean_dec(v_x_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2074_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_before_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2072_; 
v_before_2056_ = lean_ctor_get(v_head_2051_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_head_2051_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v_head_2051_, 1);
lean_dec(v_unused_2073_);
v___x_2058_ = v_head_2051_;
v_isShared_2059_ = v_isSharedCheck_2072_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_before_2056_);
lean_dec(v_head_2051_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2072_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 7);
lean_ctor_set(v___x_2058_, 1, v___x_2060_);
lean_ctor_set(v___x_2058_, 0, v_x_2049_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_x_2049_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2055_ == 0)
{
lean_ctor_set_tag(v___x_2054_, 7);
lean_ctor_set(v___x_2054_, 1, v___x_2063_);
lean_ctor_set(v___x_2054_, 0, v___x_2062_);
v___x_2065_ = v___x_2054_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = l_Lean_MessageData_ofSyntax(v_before_2056_);
v___x_2067_ = l_Lean_indentD(v___x_2066_);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2065_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v_x_2049_ = v___x_2068_;
v_x_2050_ = v_tail_2052_;
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
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1));
v___x_2079_ = l_Lean_MessageData_ofFormat(v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(lean_object* v_msgData_2080_, lean_object* v_macroStack_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2084_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2082_);
v___x_2085_ = l_Lean_Elab_pp_macroStack;
v___x_2086_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2084_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
lean_dec(v_macroStack_2081_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_msgData_2080_);
return v___x_2087_;
}
else
{
if (lean_obj_tag(v_macroStack_2081_) == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_msgData_2080_);
return v___x_2088_;
}
else
{
lean_object* v_head_2089_; lean_object* v_after_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2105_; 
v_head_2089_ = lean_ctor_get(v_macroStack_2081_, 0);
lean_inc(v_head_2089_);
v_after_2090_ = lean_ctor_get(v_head_2089_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_head_2089_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v_head_2089_, 0);
lean_dec(v_unused_2106_);
v___x_2092_ = v_head_2089_;
v_isShared_2093_ = v_isSharedCheck_2105_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_after_2090_);
lean_dec(v_head_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2105_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 7);
lean_ctor_set(v___x_2092_, 1, v___x_2094_);
lean_ctor_set(v___x_2092_, 0, v_msgData_2080_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_msgData_2080_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_msgData_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2097_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_MessageData_ofSyntax(v_after_2090_);
v___x_2100_ = l_Lean_indentD(v___x_2099_);
v_msgData_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2101_, 0, v___x_2098_);
lean_ctor_set(v_msgData_2101_, 1, v___x_2100_);
v___x_2102_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(v_msgData_2101_, v_macroStack_2081_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2107_, lean_object* v_macroStack_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2107_, v_macroStack_2108_, v___y_2109_);
lean_dec_ref(v___y_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_ref_2120_; lean_object* v_macroStack_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2134_; 
v_ref_2120_ = lean_ctor_get(v___y_2117_, 2);
v_macroStack_2121_ = lean_ctor_get(v___y_2113_, 1);
v___x_2122_ = l_Lean_Elab_getBetterRef(v_ref_2120_, v_macroStack_2121_);
v___x_2123_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2112_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
lean_inc(v_macroStack_2121_);
v___x_2125_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_a_2124_, v_macroStack_2121_, v___y_2117_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2122_);
lean_ctor_set(v___x_2130_, 1, v_a_2126_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0(lean_object* v___x_2144_, lean_object* v___x_2145_, lean_object* v_s_2146_){
_start:
{
lean_object* v_addEntryFn_2147_; lean_object* v_importedEntries_2148_; lean_object* v_state_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
v_addEntryFn_2147_ = lean_ctor_get(v___x_2144_, 3);
lean_inc(v_addEntryFn_2147_);
lean_dec_ref(v___x_2144_);
v_importedEntries_2148_ = lean_ctor_get(v_s_2146_, 0);
v_state_2149_ = lean_ctor_get(v_s_2146_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_s_2146_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v_s_2146_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_state_2149_);
lean_inc(v_importedEntries_2148_);
lean_dec(v_s_2146_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_state_2153_; lean_object* v___x_2155_; 
v_state_2153_ = lean_apply_2(v_addEntryFn_2147_, v_state_2149_, v___x_2145_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_state_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_importedEntries_2148_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_state_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2158_, lean_object* v_as_2159_, size_t v_i_2160_, size_t v_stop_2161_, lean_object* v_b_2162_){
_start:
{
lean_object* v___y_2164_; uint8_t v___x_2168_; 
v___x_2168_ = lean_usize_dec_eq(v_i_2160_, v_stop_2161_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v_index_2170_; lean_object* v_sourceString_2171_; lean_object* v_imports_2172_; lean_object* v_currNamespace_2173_; lean_object* v_openDecls_2174_; lean_object* v_options_2175_; lean_object* v_check_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2194_; 
v___x_2169_ = lean_array_uget(v_as_2159_, v_i_2160_);
v_index_2170_ = lean_ctor_get(v___x_2169_, 1);
v_sourceString_2171_ = lean_ctor_get(v___x_2169_, 2);
v_imports_2172_ = lean_ctor_get(v___x_2169_, 3);
v_currNamespace_2173_ = lean_ctor_get(v___x_2169_, 4);
v_openDecls_2174_ = lean_ctor_get(v___x_2169_, 5);
v_options_2175_ = lean_ctor_get(v___x_2169_, 6);
v_check_2176_ = lean_ctor_get(v___x_2169_, 7);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v___x_2169_, 0);
lean_dec(v_unused_2195_);
v___x_2178_ = v___x_2169_;
v_isShared_2179_ = v_isSharedCheck_2194_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_check_2176_);
lean_inc(v_options_2175_);
lean_inc(v_openDecls_2174_);
lean_inc(v_currNamespace_2173_);
lean_inc(v_imports_2172_);
lean_inc(v_sourceString_2171_);
lean_inc(v_index_2170_);
lean_dec(v___x_2169_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2194_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v_toEnvExtension_2181_; lean_object* v_asyncMode_2182_; uint8_t v_logWrites_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2180_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2181_ = lean_ctor_get(v___x_2180_, 0);
v_asyncMode_2182_ = lean_ctor_get(v_toEnvExtension_2181_, 2);
v_logWrites_2183_ = lean_ctor_get_uint8(v_toEnvExtension_2181_, sizeof(void*)*6);
lean_inc(v_declName_2158_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_declName_2158_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2184_);
v___x_2186_ = v___x_2178_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_index_2170_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_sourceString_2171_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_imports_2172_);
lean_ctor_set(v_reuseFailAlloc_2193_, 4, v_currNamespace_2173_);
lean_ctor_set(v_reuseFailAlloc_2193_, 5, v_openDecls_2174_);
lean_ctor_set(v_reuseFailAlloc_2193_, 6, v_options_2175_);
lean_ctor_set(v_reuseFailAlloc_2193_, 7, v_check_2176_);
v___x_2186_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___f_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___f_2187_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2187_, 0, v___x_2180_);
lean_closure_set(v___f_2187_, 1, v___x_2186_);
v___x_2188_ = lean_box(0);
v___x_2189_ = 1;
if (v_logWrites_2183_ == 0)
{
lean_object* v___x_2190_; 
lean_inc_ref(v_toEnvExtension_2181_);
v___x_2190_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2181_, v_b_2162_, v___f_2187_, v_asyncMode_2182_, v___x_2188_, v___x_2189_);
v___y_2164_ = v___x_2190_;
goto v___jp_2163_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_inc_ref_n(v_toEnvExtension_2181_, 2);
v___x_2191_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2181_, v_b_2162_);
lean_dec_ref(v_b_2162_);
v___x_2192_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2181_, v___x_2191_, v___f_2187_, v_asyncMode_2182_, v___x_2188_, v___x_2189_);
v___y_2164_ = v___x_2192_;
goto v___jp_2163_;
}
}
}
}
else
{
lean_dec(v_declName_2158_);
return v_b_2162_;
}
v___jp_2163_:
{
size_t v___x_2165_; size_t v___x_2166_; 
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_add(v_i_2160_, v___x_2165_);
v_i_2160_ = v___x_2166_;
v_b_2162_ = v___y_2164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2196_, lean_object* v_as_2197_, lean_object* v_i_2198_, lean_object* v_stop_2199_, lean_object* v_b_2200_){
_start:
{
size_t v_i_boxed_2201_; size_t v_stop_boxed_2202_; lean_object* v_res_2203_; 
v_i_boxed_2201_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_stop_boxed_2202_ = lean_unbox_usize(v_stop_2199_);
lean_dec(v_stop_2199_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2196_, v_as_2197_, v_i_boxed_2201_, v_stop_boxed_2202_, v_b_2200_);
lean_dec_ref(v_as_2197_);
return v_res_2203_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2209_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_ctor_set(v___x_2209_, 2, v___x_2208_);
lean_ctor_set(v___x_2209_, 3, v___x_2208_);
lean_ctor_set(v___x_2209_, 4, v___x_2208_);
lean_ctor_set(v___x_2209_, 5, v___x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2210_, lean_object* v_docs_2211_, lean_object* v_deferred_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; uint8_t v___x_2252_; 
v___x_2252_ = l_Lean_Name_isAnonymous(v_declName_2210_);
if (v___x_2252_ == 0)
{
uint8_t v___x_2253_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___x_2275_; lean_object* v_env_2276_; lean_object* v___x_2277_; 
v___x_2253_ = 1;
v___x_2275_ = lean_st_ref_get(v___y_2218_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_env_2276_);
lean_dec(v___x_2275_);
v___x_2277_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2276_, v_declName_2210_);
lean_dec_ref(v_env_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
v___y_2255_ = v___y_2216_;
v___y_2256_ = v___y_2218_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2291_; 
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2292_);
v___x_2279_ = v___x_2277_;
v_isShared_2280_ = v_isSharedCheck_2291_;
goto v_resetjp_2278_;
}
else
{
lean_dec(v___x_2277_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2291_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
if (v___x_2252_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec_ref(v_docs_2211_);
v___x_2281_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2282_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2210_, v___x_2253_);
v___x_2283_ = lean_string_append(v___x_2281_, v___x_2282_);
lean_dec_ref(v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2285_ = lean_string_append(v___x_2283_, v___x_2284_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set_tag(v___x_2279_, 3);
lean_ctor_set(v___x_2279_, 0, v___x_2285_);
v___x_2287_ = v___x_2279_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = l_Lean_MessageData_ofFormat(v___x_2287_);
v___x_2289_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2288_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2289_;
}
}
else
{
lean_del_object(v___x_2279_);
v___y_2255_ = v___y_2216_;
v___y_2256_ = v___y_2218_;
goto v___jp_2254_;
}
}
}
v___jp_2254_:
{
lean_object* v___x_2257_; lean_object* v_env_2258_; lean_object* v_nextMacroScope_2259_; lean_object* v_ngen_2260_; lean_object* v_auxDeclNGen_2261_; lean_object* v_traceState_2262_; lean_object* v_recordedDeps_2263_; lean_object* v_messages_2264_; lean_object* v_infoState_2265_; lean_object* v_snapshotTasks_2266_; lean_object* v___x_2267_; lean_object* v_env_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2257_ = lean_st_ref_take(v___y_2256_);
v_env_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc_ref(v_env_2258_);
v_nextMacroScope_2259_ = lean_ctor_get(v___x_2257_, 1);
lean_inc(v_nextMacroScope_2259_);
v_ngen_2260_ = lean_ctor_get(v___x_2257_, 2);
lean_inc_ref(v_ngen_2260_);
v_auxDeclNGen_2261_ = lean_ctor_get(v___x_2257_, 3);
lean_inc_ref(v_auxDeclNGen_2261_);
v_traceState_2262_ = lean_ctor_get(v___x_2257_, 4);
lean_inc_ref(v_traceState_2262_);
v_recordedDeps_2263_ = lean_ctor_get(v___x_2257_, 6);
lean_inc_ref(v_recordedDeps_2263_);
v_messages_2264_ = lean_ctor_get(v___x_2257_, 7);
lean_inc_ref(v_messages_2264_);
v_infoState_2265_ = lean_ctor_get(v___x_2257_, 8);
lean_inc_ref(v_infoState_2265_);
v_snapshotTasks_2266_ = lean_ctor_get(v___x_2257_, 9);
lean_inc_ref(v_snapshotTasks_2266_);
lean_dec(v___x_2257_);
v___x_2267_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2210_);
v_env_2268_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2267_, v_env_2258_, v_declName_2210_, v_docs_2211_, v___x_2253_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_array_get_size(v_deferred_2212_);
v___x_2271_ = lean_nat_dec_lt(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec(v_declName_2210_);
v___y_2221_ = v_ngen_2260_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v_nextMacroScope_2259_;
v___y_2224_ = v_auxDeclNGen_2261_;
v___y_2225_ = v_messages_2264_;
v___y_2226_ = v___y_2256_;
v___y_2227_ = v_snapshotTasks_2266_;
v___y_2228_ = v_recordedDeps_2263_;
v___y_2229_ = v_traceState_2262_;
v___y_2230_ = v_infoState_2265_;
v___y_2231_ = v_env_2268_;
goto v___jp_2220_;
}
else
{
size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = ((size_t)0ULL);
v___x_2273_ = lean_usize_of_nat(v___x_2270_);
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2210_, v_deferred_2212_, v___x_2272_, v___x_2273_, v_env_2268_);
v___y_2221_ = v_ngen_2260_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v_nextMacroScope_2259_;
v___y_2224_ = v_auxDeclNGen_2261_;
v___y_2225_ = v_messages_2264_;
v___y_2226_ = v___y_2256_;
v___y_2227_ = v_snapshotTasks_2266_;
v___y_2228_ = v_recordedDeps_2263_;
v___y_2229_ = v_traceState_2262_;
v___y_2230_ = v_infoState_2265_;
v___y_2231_ = v___x_2274_;
goto v___jp_2220_;
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v_docs_2211_);
lean_dec(v_declName_2210_);
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
v___jp_2220_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_mctx_2236_; lean_object* v_zetaDeltaFVarIds_2237_; lean_object* v_postponed_2238_; lean_object* v_diag_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2250_; 
v___x_2232_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2233_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2233_, 0, v___y_2231_);
lean_ctor_set(v___x_2233_, 1, v___y_2223_);
lean_ctor_set(v___x_2233_, 2, v___y_2221_);
lean_ctor_set(v___x_2233_, 3, v___y_2224_);
lean_ctor_set(v___x_2233_, 4, v___y_2229_);
lean_ctor_set(v___x_2233_, 5, v___x_2232_);
lean_ctor_set(v___x_2233_, 6, v___y_2228_);
lean_ctor_set(v___x_2233_, 7, v___y_2225_);
lean_ctor_set(v___x_2233_, 8, v___y_2230_);
lean_ctor_set(v___x_2233_, 9, v___y_2227_);
v___x_2234_ = lean_st_ref_put(v___y_2226_, v___x_2233_);
v___x_2235_ = lean_st_ref_take(v___y_2222_);
v_mctx_2236_ = lean_ctor_get(v___x_2235_, 0);
v_zetaDeltaFVarIds_2237_ = lean_ctor_get(v___x_2235_, 2);
v_postponed_2238_ = lean_ctor_get(v___x_2235_, 3);
v_diag_2239_ = lean_ctor_get(v___x_2235_, 4);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v___x_2235_, 1);
lean_dec(v_unused_2251_);
v___x_2241_ = v___x_2235_;
v_isShared_2242_ = v_isSharedCheck_2250_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_diag_2239_);
lean_inc(v_postponed_2238_);
lean_inc(v_zetaDeltaFVarIds_2237_);
lean_inc(v_mctx_2236_);
lean_dec(v___x_2235_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2250_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_mctx_2236_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_zetaDeltaFVarIds_2237_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_postponed_2238_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_diag_2239_);
v___x_2246_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_st_ref_put(v___y_2222_, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2243_);
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2295_, lean_object* v_docs_2296_, lean_object* v_deferred_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2295_, v_docs_2296_, v_deferred_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v_deferred_2297_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2306_, lean_object* v_binders_2307_, lean_object* v_docComment_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___x_2336_; lean_object* v_env_2337_; lean_object* v___x_2338_; 
v___x_2336_ = lean_st_ref_get(v_a_2314_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_ref(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2338_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2337_, v_declName_2306_);
lean_dec_ref(v_env_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
v___y_2317_ = v_a_2309_;
v___y_2318_ = v_a_2310_;
v___y_2319_ = v_a_2311_;
v___y_2320_ = v_a_2312_;
v___y_2321_ = v_a_2313_;
v___y_2322_ = v_a_2314_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_binders_2307_);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v___x_2338_, 0);
lean_dec(v_unused_2354_);
v___x_2340_ = v___x_2338_;
v_isShared_2341_ = v_isSharedCheck_2353_;
goto v_resetjp_2339_;
}
else
{
lean_dec(v___x_2338_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2353_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2342_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2343_ = 1;
v___x_2344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2306_, v___x_2343_);
v___x_2345_ = lean_string_append(v___x_2342_, v___x_2344_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set_tag(v___x_2340_, 3);
lean_ctor_set(v___x_2340_, 0, v___x_2347_);
v___x_2349_ = v___x_2340_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = l_Lean_MessageData_ofFormat(v___x_2349_);
v___x_2351_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2350_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2351_;
}
}
}
v___jp_2316_:
{
lean_object* v___x_2323_; 
lean_inc(v_declName_2306_);
v___x_2323_ = l_Lean_versoDocString(v_declName_2306_, v_binders_2307_, v_docComment_2308_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v_toVersoDocString_2325_; lean_object* v_deferredChecks_2326_; lean_object* v___x_2327_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_toVersoDocString_2325_ = lean_ctor_get(v_a_2324_, 0);
lean_inc_ref(v_toVersoDocString_2325_);
v_deferredChecks_2326_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_ref(v_deferredChecks_2326_);
lean_dec(v_a_2324_);
v___x_2327_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2306_, v_toVersoDocString_2325_, v_deferredChecks_2326_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec_ref(v_deferredChecks_2326_);
return v___x_2327_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_declName_2306_);
v_a_2328_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2323_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2323_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2355_, lean_object* v_binders_2356_, lean_object* v_docComment_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_addVersoDocString(v_declName_2355_, v_binders_2356_, v_docComment_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_docComment_2357_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2366_, lean_object* v_msg_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_msg_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2376_, v_msg_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(lean_object* v_msgData_2386_, lean_object* v_macroStack_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2386_, v_macroStack_2387_, v___y_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___boxed(lean_object* v_msgData_2396_, lean_object* v_macroStack_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(v_msgData_2396_, v_macroStack_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
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
lean_object* v_toCold_2593_; lean_object* v_currRecDepth_2594_; lean_object* v_ref_2595_; uint16_t v_optionFlags_2596_; uint8_t v_suppressElabErrors_2597_; uint8_t v_isRecordingDeps_2598_; lean_object* v_ref_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_toCold_2593_ = lean_ctor_get(v___y_2590_, 0);
v_currRecDepth_2594_ = lean_ctor_get(v___y_2590_, 1);
v_ref_2595_ = lean_ctor_get(v___y_2590_, 2);
v_optionFlags_2596_ = lean_ctor_get_uint16(v___y_2590_, sizeof(void*)*3);
v_suppressElabErrors_2597_ = lean_ctor_get_uint8(v___y_2590_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2598_ = lean_ctor_get_uint8(v___y_2590_, sizeof(void*)*3 + 3);
v_ref_2599_ = l_Lean_replaceRef(v_ref_2584_, v_ref_2595_);
lean_inc(v_currRecDepth_2594_);
lean_inc_ref(v_toCold_2593_);
v___x_2600_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2600_, 0, v_toCold_2593_);
lean_ctor_set(v___x_2600_, 1, v_currRecDepth_2594_);
lean_ctor_set(v___x_2600_, 2, v_ref_2599_);
lean_ctor_set_uint16(v___x_2600_, sizeof(void*)*3, v_optionFlags_2596_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*3 + 2, v_suppressElabErrors_2597_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*3 + 3, v_isRecordingDeps_2598_);
v___x_2601_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___x_2600_, v___y_2591_);
lean_dec_ref_known(v___x_2600_, 3);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2602_, lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2602_, v_msg_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v_ref_2602_);
return v_res_2611_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2614_ = l_Lean_stringToMessageData(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = l_Lean_Syntax_getArg(v_stx_2616_, v___x_2630_);
if (lean_obj_tag(v___x_2631_) == 1)
{
lean_object* v_kind_2632_; 
v_kind_2632_ = lean_ctor_get(v___x_2631_, 1);
lean_inc(v_kind_2632_);
if (lean_obj_tag(v_kind_2632_) == 1)
{
lean_object* v_pre_2633_; 
v_pre_2633_ = lean_ctor_get(v_kind_2632_, 0);
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
lean_inc(v_pre_2635_);
if (lean_obj_tag(v_pre_2635_) == 1)
{
lean_object* v_pre_2636_; 
v_pre_2636_ = lean_ctor_get(v_pre_2635_, 0);
if (lean_obj_tag(v_pre_2636_) == 0)
{
lean_object* v_args_2637_; lean_object* v_str_2638_; lean_object* v_str_2639_; lean_object* v_str_2640_; lean_object* v_str_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_args_2637_ = lean_ctor_get(v___x_2631_, 2);
lean_inc_ref(v_args_2637_);
lean_dec_ref_known(v___x_2631_, 3);
v_str_2638_ = lean_ctor_get(v_kind_2632_, 1);
lean_inc_ref(v_str_2638_);
lean_dec_ref_known(v_kind_2632_, 2);
v_str_2639_ = lean_ctor_get(v_pre_2633_, 1);
lean_inc_ref(v_str_2639_);
lean_dec_ref_known(v_pre_2633_, 2);
v_str_2640_ = lean_ctor_get(v_pre_2634_, 1);
lean_inc_ref(v_str_2640_);
lean_dec_ref_known(v_pre_2634_, 2);
v_str_2641_ = lean_ctor_get(v_pre_2635_, 1);
lean_inc_ref(v_str_2641_);
lean_dec_ref_known(v_pre_2635_, 2);
v___x_2642_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2643_ = lean_string_dec_eq(v_str_2641_, v___x_2642_);
lean_dec_ref(v_str_2641_);
if (v___x_2643_ == 0)
{
lean_dec_ref(v_str_2640_);
lean_dec_ref(v_str_2639_);
lean_dec_ref(v_str_2638_);
lean_dec_ref(v_args_2637_);
goto v___jp_2624_;
}
else
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2645_ = lean_string_dec_eq(v_str_2640_, v___x_2644_);
lean_dec_ref(v_str_2640_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v_str_2639_);
lean_dec_ref(v_str_2638_);
lean_dec_ref(v_args_2637_);
goto v___jp_2624_;
}
else
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2647_ = lean_string_dec_eq(v_str_2639_, v___x_2646_);
lean_dec_ref(v_str_2639_);
if (v___x_2647_ == 0)
{
lean_dec_ref(v_str_2638_);
lean_dec_ref(v_args_2637_);
goto v___jp_2624_;
}
else
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2649_ = lean_string_dec_eq(v_str_2638_, v___x_2648_);
lean_dec_ref(v_str_2638_);
if (v___x_2649_ == 0)
{
lean_dec_ref(v_args_2637_);
goto v___jp_2624_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_array_get_size(v_args_2637_);
v___x_2651_ = lean_unsigned_to_nat(2u);
v___x_2652_ = lean_nat_dec_eq(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_dec_ref(v_args_2637_);
goto v___jp_2624_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_array_fget(v_args_2637_, v___x_2653_);
lean_dec_ref(v_args_2637_);
if (lean_obj_tag(v___x_2654_) == 2)
{
lean_object* v_val_2655_; lean_object* v___x_2656_; 
lean_dec(v_stx_2616_);
v_val_2655_ = lean_ctor_get(v___x_2654_, 1);
lean_inc_ref(v_val_2655_);
lean_dec_ref_known(v___x_2654_, 2);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_val_2655_);
return v___x_2656_;
}
else
{
lean_dec(v___x_2654_);
goto v___jp_2624_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2635_, 2);
lean_dec_ref_known(v_pre_2634_, 2);
lean_dec_ref_known(v_pre_2633_, 2);
lean_dec_ref_known(v_kind_2632_, 2);
lean_dec_ref_known(v___x_2631_, 3);
goto v___jp_2624_;
}
}
else
{
lean_dec_ref_known(v_pre_2634_, 2);
lean_dec(v_pre_2635_);
lean_dec_ref_known(v_pre_2633_, 2);
lean_dec_ref_known(v_kind_2632_, 2);
lean_dec_ref_known(v___x_2631_, 3);
goto v___jp_2624_;
}
}
else
{
lean_dec(v_pre_2634_);
lean_dec_ref_known(v_pre_2633_, 2);
lean_dec_ref_known(v_kind_2632_, 2);
lean_dec_ref_known(v___x_2631_, 3);
goto v___jp_2624_;
}
}
else
{
lean_dec(v_pre_2633_);
lean_dec_ref_known(v_kind_2632_, 2);
lean_dec_ref_known(v___x_2631_, 3);
goto v___jp_2624_;
}
}
else
{
lean_dec(v_kind_2632_);
lean_dec_ref_known(v___x_2631_, 3);
goto v___jp_2624_;
}
}
else
{
lean_dec(v___x_2631_);
goto v___jp_2624_;
}
v___jp_2624_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2625_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2616_);
v___x_2626_ = l_Lean_MessageData_ofSyntax(v_stx_2616_);
v___x_2627_ = l_Lean_indentD(v___x_2626_);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2625_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2616_, v___x_2628_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v_stx_2616_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2666_, lean_object* v_docComment_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v___x_2675_; 
v___x_2675_ = l_Lean_Name_isAnonymous(v_declName_2666_);
if (v___x_2675_ == 0)
{
uint8_t v___x_2676_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___x_2741_; lean_object* v_env_2742_; lean_object* v___x_2743_; 
v___x_2676_ = 1;
v___x_2741_ = lean_st_ref_get(v___y_2673_);
v_env_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_ref(v_env_2742_);
lean_dec(v___x_2741_);
v___x_2743_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2742_, v_declName_2666_);
lean_dec_ref(v_env_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
v___y_2678_ = v___y_2668_;
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
v___y_2683_ = v___y_2673_;
goto v___jp_2677_;
}
else
{
lean_dec_ref_known(v___x_2743_, 1);
if (v___x_2675_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec(v_docComment_2667_);
v___x_2744_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2745_ = l_Lean_MessageData_ofConstName(v_declName_2666_, v___x_2675_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2748_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2749_;
}
else
{
v___y_2678_ = v___y_2668_;
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
v___y_2683_ = v___y_2673_;
goto v___jp_2677_;
}
}
v___jp_2677_:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2667_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2685_; 
lean_dec_ref_known(v___x_2684_, 1);
v___x_2685_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2667_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2732_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2732_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2732_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v_env_2691_; lean_object* v_nextMacroScope_2692_; lean_object* v_ngen_2693_; lean_object* v_auxDeclNGen_2694_; lean_object* v_traceState_2695_; lean_object* v_recordedDeps_2696_; lean_object* v_messages_2697_; lean_object* v_infoState_2698_; lean_object* v_snapshotTasks_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2730_; 
v___x_2690_ = lean_st_ref_take(v___y_2683_);
v_env_2691_ = lean_ctor_get(v___x_2690_, 0);
v_nextMacroScope_2692_ = lean_ctor_get(v___x_2690_, 1);
v_ngen_2693_ = lean_ctor_get(v___x_2690_, 2);
v_auxDeclNGen_2694_ = lean_ctor_get(v___x_2690_, 3);
v_traceState_2695_ = lean_ctor_get(v___x_2690_, 4);
v_recordedDeps_2696_ = lean_ctor_get(v___x_2690_, 6);
v_messages_2697_ = lean_ctor_get(v___x_2690_, 7);
v_infoState_2698_ = lean_ctor_get(v___x_2690_, 8);
v_snapshotTasks_2699_ = lean_ctor_get(v___x_2690_, 9);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v___x_2690_, 5);
lean_dec(v_unused_2731_);
v___x_2701_ = v___x_2690_;
v_isShared_2702_ = v_isSharedCheck_2730_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snapshotTasks_2699_);
lean_inc(v_infoState_2698_);
lean_inc(v_messages_2697_);
lean_inc(v_recordedDeps_2696_);
lean_inc(v_traceState_2695_);
lean_inc(v_auxDeclNGen_2694_);
lean_inc(v_ngen_2693_);
lean_inc(v_nextMacroScope_2692_);
lean_inc(v_env_2691_);
lean_dec(v___x_2690_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2730_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2703_ = l_Lean_docStringExt;
v___x_2704_ = l_String_removeLeadingSpaces(v_a_2686_);
v___x_2705_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2703_, v_env_2691_, v_declName_2666_, v___x_2704_, v___x_2676_);
v___x_2706_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 5, v___x_2706_);
lean_ctor_set(v___x_2701_, 0, v___x_2705_);
v___x_2708_ = v___x_2701_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_nextMacroScope_2692_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_ngen_2693_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_auxDeclNGen_2694_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v_traceState_2695_);
lean_ctor_set(v_reuseFailAlloc_2729_, 5, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2729_, 6, v_recordedDeps_2696_);
lean_ctor_set(v_reuseFailAlloc_2729_, 7, v_messages_2697_);
lean_ctor_set(v_reuseFailAlloc_2729_, 8, v_infoState_2698_);
lean_ctor_set(v_reuseFailAlloc_2729_, 9, v_snapshotTasks_2699_);
v___x_2708_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v_mctx_2711_; lean_object* v_zetaDeltaFVarIds_2712_; lean_object* v_postponed_2713_; lean_object* v_diag_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2727_; 
v___x_2709_ = lean_st_ref_put(v___y_2683_, v___x_2708_);
v___x_2710_ = lean_st_ref_take(v___y_2681_);
v_mctx_2711_ = lean_ctor_get(v___x_2710_, 0);
v_zetaDeltaFVarIds_2712_ = lean_ctor_get(v___x_2710_, 2);
v_postponed_2713_ = lean_ctor_get(v___x_2710_, 3);
v_diag_2714_ = lean_ctor_get(v___x_2710_, 4);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v___x_2710_, 1);
lean_dec(v_unused_2728_);
v___x_2716_ = v___x_2710_;
v_isShared_2717_ = v_isSharedCheck_2727_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_diag_2714_);
lean_inc(v_postponed_2713_);
lean_inc(v_zetaDeltaFVarIds_2712_);
lean_inc(v_mctx_2711_);
lean_dec(v___x_2710_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2727_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 1, v___x_2719_);
v___x_2721_ = v___x_2716_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_mctx_2711_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_zetaDeltaFVarIds_2712_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_postponed_2713_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_diag_2714_);
v___x_2721_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = lean_st_ref_put(v___y_2681_, v___x_2721_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2718_);
v___x_2724_ = v___x_2688_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2718_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_declName_2666_);
v_a_2733_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2685_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2685_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_dec(v_docComment_2667_);
lean_dec(v_declName_2666_);
return v___x_2684_;
}
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec(v_docComment_2667_);
lean_dec(v_declName_2666_);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2752_, lean_object* v_docComment_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2752_, v_docComment_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2762_, lean_object* v_declName_2763_, lean_object* v_binders_2764_, lean_object* v_docComment_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
if (v_isVerso_2762_ == 0)
{
lean_object* v___x_2773_; 
lean_dec(v_binders_2764_);
v___x_2773_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2763_, v_docComment_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_addVersoDocString(v_declName_2763_, v_binders_2764_, v_docComment_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_docComment_2765_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2775_, lean_object* v_declName_2776_, lean_object* v_binders_2777_, lean_object* v_docComment_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
uint8_t v_isVerso_boxed_2786_; lean_object* v_res_2787_; 
v_isVerso_boxed_2786_ = lean_unbox(v_isVerso_2775_);
v_res_2787_ = l_Lean_addDocStringOf(v_isVerso_boxed_2786_, v_declName_2776_, v_binders_2777_, v_docComment_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2788_, lean_object* v_msgData_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2788_, v_msgData_2789_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2798_, lean_object* v_msgData_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2798_, v_msgData_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v_ref_2798_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2808_, lean_object* v_ref_2809_, lean_object* v_msg_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2809_, v_msg_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2819_, lean_object* v_ref_2820_, lean_object* v_msg_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2819_, v_ref_2820_, v_msg_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v_ref_2820_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2830_, lean_object* v_t_2831_){
_start:
{
if (lean_obj_tag(v_t_2831_) == 0)
{
lean_object* v_k_2832_; lean_object* v_v_2833_; lean_object* v_l_2834_; lean_object* v_r_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_3489_; 
v_k_2832_ = lean_ctor_get(v_t_2831_, 1);
v_v_2833_ = lean_ctor_get(v_t_2831_, 2);
v_l_2834_ = lean_ctor_get(v_t_2831_, 3);
v_r_2835_ = lean_ctor_get(v_t_2831_, 4);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_t_2831_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v_t_2831_, 0);
lean_dec(v_unused_3490_);
v___x_2837_ = v_t_2831_;
v_isShared_2838_ = v_isSharedCheck_3489_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_r_2835_);
lean_inc(v_l_2834_);
lean_inc(v_v_2833_);
lean_inc(v_k_2832_);
lean_dec(v_t_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_3489_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
uint8_t v___x_2839_; 
v___x_2839_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2830_, v_k_2832_);
switch(v___x_2839_)
{
case 0:
{
lean_object* v_impl_2840_; lean_object* v___x_2841_; 
v_impl_2840_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2830_, v_l_2834_);
v___x_2841_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2840_) == 0)
{
if (lean_obj_tag(v_r_2835_) == 0)
{
lean_object* v_size_2842_; lean_object* v_size_2843_; lean_object* v_k_2844_; lean_object* v_v_2845_; lean_object* v_l_2846_; lean_object* v_r_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_size_2842_ = lean_ctor_get(v_impl_2840_, 0);
v_size_2843_ = lean_ctor_get(v_r_2835_, 0);
v_k_2844_ = lean_ctor_get(v_r_2835_, 1);
v_v_2845_ = lean_ctor_get(v_r_2835_, 2);
v_l_2846_ = lean_ctor_get(v_r_2835_, 3);
lean_inc(v_l_2846_);
v_r_2847_ = lean_ctor_get(v_r_2835_, 4);
v___x_2848_ = lean_unsigned_to_nat(3u);
v___x_2849_ = lean_nat_mul(v___x_2848_, v_size_2842_);
v___x_2850_ = lean_nat_dec_lt(v___x_2849_, v_size_2843_);
lean_dec(v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
lean_dec(v_l_2846_);
v___x_2851_ = lean_nat_add(v___x_2841_, v_size_2842_);
v___x_2852_ = lean_nat_add(v___x_2851_, v_size_2843_);
lean_dec(v___x_2851_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 3, v_impl_2840_);
lean_ctor_set(v___x_2837_, 0, v___x_2852_);
v___x_2854_ = v___x_2837_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_impl_2840_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_r_2835_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
else
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2919_; 
lean_inc(v_r_2847_);
lean_inc(v_v_2845_);
lean_inc(v_k_2844_);
lean_inc(v_size_2843_);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; 
v_unused_2920_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_r_2835_, 2);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_r_2835_, 1);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_r_2835_, 0);
lean_dec(v_unused_2924_);
v___x_2857_ = v_r_2835_;
v_isShared_2858_ = v_isSharedCheck_2919_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v_r_2835_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2919_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_size_2859_; lean_object* v_k_2860_; lean_object* v_v_2861_; lean_object* v_l_2862_; lean_object* v_r_2863_; lean_object* v_size_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_size_2859_ = lean_ctor_get(v_l_2846_, 0);
v_k_2860_ = lean_ctor_get(v_l_2846_, 1);
v_v_2861_ = lean_ctor_get(v_l_2846_, 2);
v_l_2862_ = lean_ctor_get(v_l_2846_, 3);
v_r_2863_ = lean_ctor_get(v_l_2846_, 4);
v_size_2864_ = lean_ctor_get(v_r_2847_, 0);
v___x_2865_ = lean_unsigned_to_nat(2u);
v___x_2866_ = lean_nat_mul(v___x_2865_, v_size_2864_);
v___x_2867_ = lean_nat_dec_lt(v_size_2859_, v___x_2866_);
lean_dec(v___x_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2895_; 
lean_inc(v_r_2863_);
lean_inc(v_l_2862_);
lean_inc(v_v_2861_);
lean_inc(v_k_2860_);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_l_2846_);
if (v_isSharedCheck_2895_ == 0)
{
lean_object* v_unused_2896_; lean_object* v_unused_2897_; lean_object* v_unused_2898_; lean_object* v_unused_2899_; lean_object* v_unused_2900_; 
v_unused_2896_ = lean_ctor_get(v_l_2846_, 4);
lean_dec(v_unused_2896_);
v_unused_2897_ = lean_ctor_get(v_l_2846_, 3);
lean_dec(v_unused_2897_);
v_unused_2898_ = lean_ctor_get(v_l_2846_, 2);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_l_2846_, 1);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_l_2846_, 0);
lean_dec(v_unused_2900_);
v___x_2869_ = v_l_2846_;
v_isShared_2870_ = v_isSharedCheck_2895_;
goto v_resetjp_2868_;
}
else
{
lean_dec(v_l_2846_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2895_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2885_; 
v___x_2871_ = lean_nat_add(v___x_2841_, v_size_2842_);
v___x_2872_ = lean_nat_add(v___x_2871_, v_size_2843_);
lean_dec(v_size_2843_);
if (lean_obj_tag(v_l_2862_) == 0)
{
lean_object* v_size_2893_; 
v_size_2893_ = lean_ctor_get(v_l_2862_, 0);
lean_inc(v_size_2893_);
v___y_2885_ = v_size_2893_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_unsigned_to_nat(0u);
v___y_2885_ = v___x_2894_;
goto v___jp_2884_;
}
v___jp_2873_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = lean_nat_add(v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec(v___y_2875_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 4, v_r_2847_);
lean_ctor_set(v___x_2869_, 3, v_r_2863_);
lean_ctor_set(v___x_2869_, 2, v_v_2845_);
lean_ctor_set(v___x_2869_, 1, v_k_2844_);
lean_ctor_set(v___x_2869_, 0, v___x_2877_);
v___x_2879_ = v___x_2869_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_k_2844_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_v_2845_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_r_2863_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v_r_2847_);
v___x_2879_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2881_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 4, v___x_2879_);
lean_ctor_set(v___x_2857_, 3, v___y_2874_);
lean_ctor_set(v___x_2857_, 2, v_v_2861_);
lean_ctor_set(v___x_2857_, 1, v_k_2860_);
lean_ctor_set(v___x_2857_, 0, v___x_2872_);
v___x_2881_ = v___x_2857_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_k_2860_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_v_2861_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v___y_2874_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2886_ = lean_nat_add(v___x_2871_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec(v___x_2871_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_l_2862_);
lean_ctor_set(v___x_2837_, 3, v_impl_2840_);
lean_ctor_set(v___x_2837_, 0, v___x_2886_);
v___x_2888_ = v___x_2837_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2892_, 3, v_impl_2840_);
lean_ctor_set(v_reuseFailAlloc_2892_, 4, v_l_2862_);
v___x_2888_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_nat_add(v___x_2841_, v_size_2864_);
if (lean_obj_tag(v_r_2863_) == 0)
{
lean_object* v_size_2890_; 
v_size_2890_ = lean_ctor_get(v_r_2863_, 0);
lean_inc(v_size_2890_);
v___y_2874_ = v___x_2888_;
v___y_2875_ = v___x_2889_;
v___y_2876_ = v_size_2890_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_unsigned_to_nat(0u);
v___y_2874_ = v___x_2888_;
v___y_2875_ = v___x_2889_;
v___y_2876_ = v___x_2891_;
goto v___jp_2873_;
}
}
}
}
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
lean_del_object(v___x_2837_);
v___x_2901_ = lean_nat_add(v___x_2841_, v_size_2842_);
v___x_2902_ = lean_nat_add(v___x_2901_, v_size_2843_);
lean_dec(v_size_2843_);
v___x_2903_ = lean_nat_add(v___x_2901_, v_size_2859_);
lean_dec(v___x_2901_);
lean_inc_ref(v_impl_2840_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 4, v_l_2846_);
lean_ctor_set(v___x_2857_, 3, v_impl_2840_);
lean_ctor_set(v___x_2857_, 2, v_v_2833_);
lean_ctor_set(v___x_2857_, 1, v_k_2832_);
lean_ctor_set(v___x_2857_, 0, v___x_2903_);
v___x_2905_ = v___x_2857_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_impl_2840_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_l_2846_);
v___x_2905_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
v_isSharedCheck_2912_ = !lean_is_exclusive(v_impl_2840_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; 
v_unused_2913_ = lean_ctor_get(v_impl_2840_, 4);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v_impl_2840_, 3);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_impl_2840_, 2);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_impl_2840_, 1);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_impl_2840_, 0);
lean_dec(v_unused_2917_);
v___x_2907_ = v_impl_2840_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_dec(v_impl_2840_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 4, v_r_2847_);
lean_ctor_set(v___x_2907_, 3, v___x_2905_);
lean_ctor_set(v___x_2907_, 2, v_v_2845_);
lean_ctor_set(v___x_2907_, 1, v_k_2844_);
lean_ctor_set(v___x_2907_, 0, v___x_2902_);
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_k_2844_);
lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_v_2845_);
lean_ctor_set(v_reuseFailAlloc_2911_, 3, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_r_2847_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v_size_2925_ = lean_ctor_get(v_impl_2840_, 0);
v___x_2926_ = lean_nat_add(v___x_2841_, v_size_2925_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 3, v_impl_2840_);
lean_ctor_set(v___x_2837_, 0, v___x_2926_);
v___x_2928_ = v___x_2837_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_impl_2840_);
lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_r_2835_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
if (lean_obj_tag(v_r_2835_) == 0)
{
lean_object* v_l_2930_; 
v_l_2930_ = lean_ctor_get(v_r_2835_, 3);
lean_inc(v_l_2930_);
if (lean_obj_tag(v_l_2930_) == 0)
{
lean_object* v_r_2931_; 
v_r_2931_ = lean_ctor_get(v_r_2835_, 4);
lean_inc(v_r_2931_);
if (lean_obj_tag(v_r_2931_) == 0)
{
lean_object* v_size_2932_; lean_object* v_k_2933_; lean_object* v_v_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2947_; 
v_size_2932_ = lean_ctor_get(v_r_2835_, 0);
v_k_2933_ = lean_ctor_get(v_r_2835_, 1);
v_v_2934_ = lean_ctor_get(v_r_2835_, 2);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; lean_object* v_unused_2949_; 
v_unused_2948_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_2948_);
v_unused_2949_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_2949_);
v___x_2936_ = v_r_2835_;
v_isShared_2937_ = v_isSharedCheck_2947_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_v_2934_);
lean_inc(v_k_2933_);
lean_inc(v_size_2932_);
lean_dec(v_r_2835_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2947_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_size_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
v_size_2938_ = lean_ctor_get(v_l_2930_, 0);
v___x_2939_ = lean_nat_add(v___x_2841_, v_size_2932_);
lean_dec(v_size_2932_);
v___x_2940_ = lean_nat_add(v___x_2841_, v_size_2938_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 4, v_l_2930_);
lean_ctor_set(v___x_2936_, 3, v_impl_2840_);
lean_ctor_set(v___x_2936_, 2, v_v_2833_);
lean_ctor_set(v___x_2936_, 1, v_k_2832_);
lean_ctor_set(v___x_2936_, 0, v___x_2940_);
v___x_2942_ = v___x_2936_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v_impl_2840_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_l_2930_);
v___x_2942_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2944_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_r_2931_);
lean_ctor_set(v___x_2837_, 3, v___x_2942_);
lean_ctor_set(v___x_2837_, 2, v_v_2934_);
lean_ctor_set(v___x_2837_, 1, v_k_2933_);
lean_ctor_set(v___x_2837_, 0, v___x_2939_);
v___x_2944_ = v___x_2837_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_k_2933_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_v_2934_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_r_2931_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_k_2950_; lean_object* v_v_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2974_; 
v_k_2950_ = lean_ctor_get(v_r_2835_, 1);
v_v_2951_ = lean_ctor_get(v_r_2835_, 2);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; lean_object* v_unused_2976_; lean_object* v_unused_2977_; 
v_unused_2975_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_2975_);
v_unused_2976_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_2976_);
v_unused_2977_ = lean_ctor_get(v_r_2835_, 0);
lean_dec(v_unused_2977_);
v___x_2953_ = v_r_2835_;
v_isShared_2954_ = v_isSharedCheck_2974_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_v_2951_);
lean_inc(v_k_2950_);
lean_dec(v_r_2835_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2974_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_k_2955_; lean_object* v_v_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2970_; 
v_k_2955_ = lean_ctor_get(v_l_2930_, 1);
v_v_2956_ = lean_ctor_get(v_l_2930_, 2);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_l_2930_);
if (v_isSharedCheck_2970_ == 0)
{
lean_object* v_unused_2971_; lean_object* v_unused_2972_; lean_object* v_unused_2973_; 
v_unused_2971_ = lean_ctor_get(v_l_2930_, 4);
lean_dec(v_unused_2971_);
v_unused_2972_ = lean_ctor_get(v_l_2930_, 3);
lean_dec(v_unused_2972_);
v_unused_2973_ = lean_ctor_get(v_l_2930_, 0);
lean_dec(v_unused_2973_);
v___x_2958_ = v_l_2930_;
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_v_2956_);
lean_inc(v_k_2955_);
lean_dec(v_l_2930_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = lean_unsigned_to_nat(3u);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 4, v_r_2931_);
lean_ctor_set(v___x_2958_, 3, v_r_2931_);
lean_ctor_set(v___x_2958_, 2, v_v_2833_);
lean_ctor_set(v___x_2958_, 1, v_k_2832_);
lean_ctor_set(v___x_2958_, 0, v___x_2841_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_r_2931_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_r_2931_);
v___x_2962_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2964_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 3, v_r_2931_);
lean_ctor_set(v___x_2953_, 0, v___x_2841_);
v___x_2964_ = v___x_2953_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_k_2950_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_v_2951_);
lean_ctor_set(v_reuseFailAlloc_2968_, 3, v_r_2931_);
lean_ctor_set(v_reuseFailAlloc_2968_, 4, v_r_2931_);
v___x_2964_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2966_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v___x_2964_);
lean_ctor_set(v___x_2837_, 3, v___x_2962_);
lean_ctor_set(v___x_2837_, 2, v_v_2956_);
lean_ctor_set(v___x_2837_, 1, v_k_2955_);
lean_ctor_set(v___x_2837_, 0, v___x_2960_);
v___x_2966_ = v___x_2837_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_k_2955_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_v_2956_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2978_; 
v_r_2978_ = lean_ctor_get(v_r_2835_, 4);
lean_inc(v_r_2978_);
if (lean_obj_tag(v_r_2978_) == 0)
{
lean_object* v_k_2979_; lean_object* v_v_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2991_; 
v_k_2979_ = lean_ctor_get(v_r_2835_, 1);
v_v_2980_ = lean_ctor_get(v_r_2835_, 2);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; lean_object* v_unused_2993_; lean_object* v_unused_2994_; 
v_unused_2992_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_r_2835_, 0);
lean_dec(v_unused_2994_);
v___x_2982_ = v_r_2835_;
v_isShared_2983_ = v_isSharedCheck_2991_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_v_2980_);
lean_inc(v_k_2979_);
lean_dec(v_r_2835_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2991_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2984_ = lean_unsigned_to_nat(3u);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 4, v_l_2930_);
lean_ctor_set(v___x_2982_, 2, v_v_2833_);
lean_ctor_set(v___x_2982_, 1, v_k_2832_);
lean_ctor_set(v___x_2982_, 0, v___x_2841_);
v___x_2986_ = v___x_2982_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_l_2930_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_l_2930_);
v___x_2986_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2988_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_r_2978_);
lean_ctor_set(v___x_2837_, 3, v___x_2986_);
lean_ctor_set(v___x_2837_, 2, v_v_2980_);
lean_ctor_set(v___x_2837_, 1, v_k_2979_);
lean_ctor_set(v___x_2837_, 0, v___x_2984_);
v___x_2988_ = v___x_2837_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_k_2979_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_v_2980_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v_r_2978_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_size_2995_; lean_object* v_k_2996_; lean_object* v_v_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3008_; 
v_size_2995_ = lean_ctor_get(v_r_2835_, 0);
v_k_2996_ = lean_ctor_get(v_r_2835_, 1);
v_v_2997_ = lean_ctor_get(v_r_2835_, 2);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; lean_object* v_unused_3010_; 
v_unused_3009_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_3009_);
v_unused_3010_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_3010_);
v___x_2999_ = v_r_2835_;
v_isShared_3000_ = v_isSharedCheck_3008_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_v_2997_);
lean_inc(v_k_2996_);
lean_inc(v_size_2995_);
lean_dec(v_r_2835_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3008_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 3, v_r_2978_);
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_size_2995_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_k_2996_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_v_2997_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v_r_2978_);
lean_ctor_set(v_reuseFailAlloc_3007_, 4, v_r_2978_);
v___x_3002_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = lean_unsigned_to_nat(2u);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v___x_3002_);
lean_ctor_set(v___x_2837_, 3, v_r_2978_);
lean_ctor_set(v___x_2837_, 0, v___x_3003_);
v___x_3005_ = v___x_2837_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_r_2978_);
lean_ctor_set(v_reuseFailAlloc_3006_, 4, v___x_3002_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
else
{
lean_object* v___x_3012_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 3, v_r_2835_);
lean_ctor_set(v___x_2837_, 0, v___x_2841_);
v___x_3012_ = v___x_2837_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_r_2835_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_r_2835_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2837_);
lean_dec(v_v_2833_);
lean_dec(v_k_2832_);
if (lean_obj_tag(v_l_2834_) == 0)
{
if (lean_obj_tag(v_r_2835_) == 0)
{
lean_object* v_size_3014_; lean_object* v_k_3015_; lean_object* v_v_3016_; lean_object* v_l_3017_; lean_object* v_r_3018_; lean_object* v_size_3019_; lean_object* v_k_3020_; lean_object* v_v_3021_; lean_object* v_l_3022_; lean_object* v_r_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v_size_3014_ = lean_ctor_get(v_l_2834_, 0);
v_k_3015_ = lean_ctor_get(v_l_2834_, 1);
v_v_3016_ = lean_ctor_get(v_l_2834_, 2);
v_l_3017_ = lean_ctor_get(v_l_2834_, 3);
v_r_3018_ = lean_ctor_get(v_l_2834_, 4);
lean_inc(v_r_3018_);
v_size_3019_ = lean_ctor_get(v_r_2835_, 0);
v_k_3020_ = lean_ctor_get(v_r_2835_, 1);
v_v_3021_ = lean_ctor_get(v_r_2835_, 2);
v_l_3022_ = lean_ctor_get(v_r_2835_, 3);
lean_inc(v_l_3022_);
v_r_3023_ = lean_ctor_get(v_r_2835_, 4);
v___x_3024_ = lean_unsigned_to_nat(1u);
v___x_3025_ = lean_nat_dec_lt(v_size_3014_, v_size_3019_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3161_; 
lean_inc(v_l_3017_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; lean_object* v_unused_3166_; 
v_unused_3162_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_l_2834_, 2);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_l_2834_, 1);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3166_);
v___x_3027_ = v_l_2834_;
v_isShared_3028_ = v_isSharedCheck_3161_;
goto v_resetjp_3026_;
}
else
{
lean_dec(v_l_2834_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3161_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v_tree_3030_; 
v___x_3029_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3015_, v_v_3016_, v_l_3017_, v_r_3018_);
v_tree_3030_ = lean_ctor_get(v___x_3029_, 2);
if (lean_obj_tag(v_tree_3030_) == 0)
{
lean_object* v_k_3031_; lean_object* v_v_3032_; lean_object* v_size_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
lean_inc_ref(v_tree_3030_);
v_k_3031_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_k_3031_);
v_v_3032_ = lean_ctor_get(v___x_3029_, 1);
lean_inc(v_v_3032_);
lean_dec_ref(v___x_3029_);
v_size_3033_ = lean_ctor_get(v_tree_3030_, 0);
v___x_3034_ = lean_unsigned_to_nat(3u);
v___x_3035_ = lean_nat_mul(v___x_3034_, v_size_3033_);
v___x_3036_ = lean_nat_dec_lt(v___x_3035_, v_size_3019_);
lean_dec(v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec(v_l_3022_);
v___x_3037_ = lean_nat_add(v___x_3024_, v_size_3033_);
v___x_3038_ = lean_nat_add(v___x_3037_, v_size_3019_);
lean_dec(v___x_3037_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v_r_2835_);
lean_ctor_set(v___x_3027_, 3, v_tree_3030_);
lean_ctor_set(v___x_3027_, 2, v_v_3032_);
lean_ctor_set(v___x_3027_, 1, v_k_3031_);
lean_ctor_set(v___x_3027_, 0, v___x_3038_);
v___x_3040_ = v___x_3027_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_k_3031_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_v_3032_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v_tree_3030_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_r_2835_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
else
{
lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3096_; 
lean_inc(v_r_3023_);
lean_inc(v_v_3021_);
lean_inc(v_k_3020_);
lean_inc(v_size_3019_);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; lean_object* v_unused_3098_; lean_object* v_unused_3099_; lean_object* v_unused_3100_; lean_object* v_unused_3101_; 
v_unused_3097_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_3097_);
v_unused_3098_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_r_2835_, 2);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_r_2835_, 1);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_r_2835_, 0);
lean_dec(v_unused_3101_);
v___x_3043_ = v_r_2835_;
v_isShared_3044_ = v_isSharedCheck_3096_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v_r_2835_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3096_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_size_3045_; lean_object* v_k_3046_; lean_object* v_v_3047_; lean_object* v_l_3048_; lean_object* v_r_3049_; lean_object* v_size_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v_size_3045_ = lean_ctor_get(v_l_3022_, 0);
v_k_3046_ = lean_ctor_get(v_l_3022_, 1);
v_v_3047_ = lean_ctor_get(v_l_3022_, 2);
v_l_3048_ = lean_ctor_get(v_l_3022_, 3);
v_r_3049_ = lean_ctor_get(v_l_3022_, 4);
v_size_3050_ = lean_ctor_get(v_r_3023_, 0);
v___x_3051_ = lean_unsigned_to_nat(2u);
v___x_3052_ = lean_nat_mul(v___x_3051_, v_size_3050_);
v___x_3053_ = lean_nat_dec_lt(v_size_3045_, v___x_3052_);
lean_dec(v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3081_; 
lean_inc(v_r_3049_);
lean_inc(v_l_3048_);
lean_inc(v_v_3047_);
lean_inc(v_k_3046_);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_l_3022_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; lean_object* v_unused_3083_; lean_object* v_unused_3084_; lean_object* v_unused_3085_; lean_object* v_unused_3086_; 
v_unused_3082_ = lean_ctor_get(v_l_3022_, 4);
lean_dec(v_unused_3082_);
v_unused_3083_ = lean_ctor_get(v_l_3022_, 3);
lean_dec(v_unused_3083_);
v_unused_3084_ = lean_ctor_get(v_l_3022_, 2);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v_l_3022_, 1);
lean_dec(v_unused_3085_);
v_unused_3086_ = lean_ctor_get(v_l_3022_, 0);
lean_dec(v_unused_3086_);
v___x_3055_ = v_l_3022_;
v_isShared_3056_ = v_isSharedCheck_3081_;
goto v_resetjp_3054_;
}
else
{
lean_dec(v_l_3022_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3081_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3071_; 
v___x_3057_ = lean_nat_add(v___x_3024_, v_size_3033_);
v___x_3058_ = lean_nat_add(v___x_3057_, v_size_3019_);
lean_dec(v_size_3019_);
if (lean_obj_tag(v_l_3048_) == 0)
{
lean_object* v_size_3079_; 
v_size_3079_ = lean_ctor_get(v_l_3048_, 0);
lean_inc(v_size_3079_);
v___y_3071_ = v_size_3079_;
goto v___jp_3070_;
}
else
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_unsigned_to_nat(0u);
v___y_3071_ = v___x_3080_;
goto v___jp_3070_;
}
v___jp_3059_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_nat_add(v___y_3060_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec(v___y_3060_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 4, v_r_3023_);
lean_ctor_set(v___x_3055_, 3, v_r_3049_);
lean_ctor_set(v___x_3055_, 2, v_v_3021_);
lean_ctor_set(v___x_3055_, 1, v_k_3020_);
lean_ctor_set(v___x_3055_, 0, v___x_3063_);
v___x_3065_ = v___x_3055_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_r_3049_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_r_3023_);
v___x_3065_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3067_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 4, v___x_3065_);
lean_ctor_set(v___x_3043_, 3, v___y_3061_);
lean_ctor_set(v___x_3043_, 2, v_v_3047_);
lean_ctor_set(v___x_3043_, 1, v_k_3046_);
lean_ctor_set(v___x_3043_, 0, v___x_3058_);
v___x_3067_ = v___x_3043_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_k_3046_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_v_3047_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v___y_3061_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
v___jp_3070_:
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3072_ = lean_nat_add(v___x_3057_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec(v___x_3057_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v_l_3048_);
lean_ctor_set(v___x_3027_, 3, v_tree_3030_);
lean_ctor_set(v___x_3027_, 2, v_v_3032_);
lean_ctor_set(v___x_3027_, 1, v_k_3031_);
lean_ctor_set(v___x_3027_, 0, v___x_3072_);
v___x_3074_ = v___x_3027_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_k_3031_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v_v_3032_);
lean_ctor_set(v_reuseFailAlloc_3078_, 3, v_tree_3030_);
lean_ctor_set(v_reuseFailAlloc_3078_, 4, v_l_3048_);
v___x_3074_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_nat_add(v___x_3024_, v_size_3050_);
if (lean_obj_tag(v_r_3049_) == 0)
{
lean_object* v_size_3076_; 
v_size_3076_ = lean_ctor_get(v_r_3049_, 0);
lean_inc(v_size_3076_);
v___y_3060_ = v___x_3075_;
v___y_3061_ = v___x_3074_;
v___y_3062_ = v_size_3076_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_unsigned_to_nat(0u);
v___y_3060_ = v___x_3075_;
v___y_3061_ = v___x_3074_;
v___y_3062_ = v___x_3077_;
goto v___jp_3059_;
}
}
}
}
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3087_ = lean_nat_add(v___x_3024_, v_size_3033_);
v___x_3088_ = lean_nat_add(v___x_3087_, v_size_3019_);
lean_dec(v_size_3019_);
v___x_3089_ = lean_nat_add(v___x_3087_, v_size_3045_);
lean_dec(v___x_3087_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 4, v_l_3022_);
lean_ctor_set(v___x_3043_, 3, v_tree_3030_);
lean_ctor_set(v___x_3043_, 2, v_v_3032_);
lean_ctor_set(v___x_3043_, 1, v_k_3031_);
lean_ctor_set(v___x_3043_, 0, v___x_3089_);
v___x_3091_ = v___x_3043_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_k_3031_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_v_3032_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_tree_3030_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_l_3022_);
v___x_3091_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v_r_3023_);
lean_ctor_set(v___x_3027_, 3, v___x_3091_);
lean_ctor_set(v___x_3027_, 2, v_v_3021_);
lean_ctor_set(v___x_3027_, 1, v_k_3020_);
lean_ctor_set(v___x_3027_, 0, v___x_3088_);
v___x_3093_ = v___x_3027_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_r_3023_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
else
{
lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3155_; 
lean_inc(v_r_3023_);
lean_inc(v_v_3021_);
lean_inc(v_k_3020_);
lean_inc(v_size_3019_);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; lean_object* v_unused_3157_; lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; 
v_unused_3156_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_3156_);
v_unused_3157_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_r_2835_, 2);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_r_2835_, 1);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_r_2835_, 0);
lean_dec(v_unused_3160_);
v___x_3103_ = v_r_2835_;
v_isShared_3104_ = v_isSharedCheck_3155_;
goto v_resetjp_3102_;
}
else
{
lean_dec(v_r_2835_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3155_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
if (lean_obj_tag(v_l_3022_) == 0)
{
if (lean_obj_tag(v_r_3023_) == 0)
{
lean_object* v_k_3105_; lean_object* v_v_3106_; lean_object* v_size_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
lean_inc(v_tree_3030_);
v_k_3105_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_k_3105_);
v_v_3106_ = lean_ctor_get(v___x_3029_, 1);
lean_inc(v_v_3106_);
lean_dec_ref(v___x_3029_);
v_size_3107_ = lean_ctor_get(v_l_3022_, 0);
v___x_3108_ = lean_nat_add(v___x_3024_, v_size_3019_);
lean_dec(v_size_3019_);
v___x_3109_ = lean_nat_add(v___x_3024_, v_size_3107_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 4, v_l_3022_);
lean_ctor_set(v___x_3103_, 3, v_tree_3030_);
lean_ctor_set(v___x_3103_, 2, v_v_3106_);
lean_ctor_set(v___x_3103_, 1, v_k_3105_);
lean_ctor_set(v___x_3103_, 0, v___x_3109_);
v___x_3111_ = v___x_3103_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_k_3105_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_v_3106_);
lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_tree_3030_);
lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_l_3022_);
v___x_3111_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v_r_3023_);
lean_ctor_set(v___x_3027_, 3, v___x_3111_);
lean_ctor_set(v___x_3027_, 2, v_v_3021_);
lean_ctor_set(v___x_3027_, 1, v_k_3020_);
lean_ctor_set(v___x_3027_, 0, v___x_3108_);
v___x_3113_ = v___x_3027_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_r_3023_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
lean_object* v_k_3116_; lean_object* v_v_3117_; lean_object* v_k_3118_; lean_object* v_v_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_size_3019_);
v_k_3116_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_k_3116_);
v_v_3117_ = lean_ctor_get(v___x_3029_, 1);
lean_inc(v_v_3117_);
lean_dec_ref(v___x_3029_);
v_k_3118_ = lean_ctor_get(v_l_3022_, 1);
v_v_3119_ = lean_ctor_get(v_l_3022_, 2);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_l_3022_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; lean_object* v_unused_3135_; lean_object* v_unused_3136_; 
v_unused_3134_ = lean_ctor_get(v_l_3022_, 4);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_l_3022_, 3);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_l_3022_, 0);
lean_dec(v_unused_3136_);
v___x_3121_ = v_l_3022_;
v_isShared_3122_ = v_isSharedCheck_3133_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_v_3119_);
lean_inc(v_k_3118_);
lean_dec(v_l_3022_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3133_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3123_ = lean_unsigned_to_nat(3u);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 4, v_r_3023_);
lean_ctor_set(v___x_3121_, 3, v_r_3023_);
lean_ctor_set(v___x_3121_, 2, v_v_3117_);
lean_ctor_set(v___x_3121_, 1, v_k_3116_);
lean_ctor_set(v___x_3121_, 0, v___x_3024_);
v___x_3125_ = v___x_3121_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_k_3116_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_v_3117_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_r_3023_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_r_3023_);
v___x_3125_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3127_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 3, v_r_3023_);
lean_ctor_set(v___x_3103_, 0, v___x_3024_);
v___x_3127_ = v___x_3103_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_r_3023_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_r_3023_);
v___x_3127_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3129_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v___x_3127_);
lean_ctor_set(v___x_3027_, 3, v___x_3125_);
lean_ctor_set(v___x_3027_, 2, v_v_3119_);
lean_ctor_set(v___x_3027_, 1, v_k_3118_);
lean_ctor_set(v___x_3027_, 0, v___x_3123_);
v___x_3129_ = v___x_3027_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_k_3118_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_v_3119_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3023_) == 0)
{
lean_object* v_k_3137_; lean_object* v_v_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
lean_dec(v_size_3019_);
v_k_3137_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_k_3137_);
v_v_3138_ = lean_ctor_get(v___x_3029_, 1);
lean_inc(v_v_3138_);
lean_dec_ref(v___x_3029_);
v___x_3139_ = lean_unsigned_to_nat(3u);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 4, v_l_3022_);
lean_ctor_set(v___x_3103_, 2, v_v_3138_);
lean_ctor_set(v___x_3103_, 1, v_k_3137_);
lean_ctor_set(v___x_3103_, 0, v___x_3024_);
v___x_3141_ = v___x_3103_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_k_3137_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_v_3138_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_l_3022_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_l_3022_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v_r_3023_);
lean_ctor_set(v___x_3027_, 3, v___x_3141_);
lean_ctor_set(v___x_3027_, 2, v_v_3021_);
lean_ctor_set(v___x_3027_, 1, v_k_3020_);
lean_ctor_set(v___x_3027_, 0, v___x_3139_);
v___x_3143_ = v___x_3027_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v_r_3023_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v_k_3146_; lean_object* v_v_3147_; lean_object* v___x_3149_; 
v_k_3146_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_k_3146_);
v_v_3147_ = lean_ctor_get(v___x_3029_, 1);
lean_inc(v_v_3147_);
lean_dec_ref(v___x_3029_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 3, v_r_3023_);
v___x_3149_ = v___x_3103_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_size_3019_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_r_3023_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v_r_3023_);
v___x_3149_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3150_ = lean_unsigned_to_nat(2u);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v___x_3149_);
lean_ctor_set(v___x_3027_, 3, v_r_3023_);
lean_ctor_set(v___x_3027_, 2, v_v_3147_);
lean_ctor_set(v___x_3027_, 1, v_k_3146_);
lean_ctor_set(v___x_3027_, 0, v___x_3150_);
v___x_3152_ = v___x_3027_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_k_3146_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_v_3147_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_r_3023_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v___x_3149_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
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
lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3319_; 
lean_inc(v_r_3023_);
lean_inc(v_v_3021_);
lean_inc(v_k_3020_);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_r_2835_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; lean_object* v_unused_3321_; lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; 
v_unused_3320_ = lean_ctor_get(v_r_2835_, 4);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_r_2835_, 3);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_r_2835_, 2);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_r_2835_, 1);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_r_2835_, 0);
lean_dec(v_unused_3324_);
v___x_3168_ = v_r_2835_;
v_isShared_3169_ = v_isSharedCheck_3319_;
goto v_resetjp_3167_;
}
else
{
lean_dec(v_r_2835_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3319_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v_tree_3171_; 
v___x_3170_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3020_, v_v_3021_, v_l_3022_, v_r_3023_);
v_tree_3171_ = lean_ctor_get(v___x_3170_, 2);
lean_inc(v_tree_3171_);
if (lean_obj_tag(v_tree_3171_) == 0)
{
lean_object* v_k_3172_; lean_object* v_v_3173_; lean_object* v_size_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_k_3172_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_k_3172_);
v_v_3173_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_v_3173_);
lean_dec_ref(v___x_3170_);
v_size_3174_ = lean_ctor_get(v_tree_3171_, 0);
v___x_3175_ = lean_unsigned_to_nat(3u);
v___x_3176_ = lean_nat_mul(v___x_3175_, v_size_3174_);
v___x_3177_ = lean_nat_dec_lt(v___x_3176_, v_size_3014_);
lean_dec(v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_dec(v_r_3018_);
v___x_3178_ = lean_nat_add(v___x_3024_, v_size_3014_);
v___x_3179_ = lean_nat_add(v___x_3178_, v_size_3174_);
lean_dec(v___x_3178_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_tree_3171_);
lean_ctor_set(v___x_3168_, 3, v_l_2834_);
lean_ctor_set(v___x_3168_, 2, v_v_3173_);
lean_ctor_set(v___x_3168_, 1, v_k_3172_);
lean_ctor_set(v___x_3168_, 0, v___x_3179_);
v___x_3181_ = v___x_3168_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_k_3172_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_v_3173_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_l_2834_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_tree_3171_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
else
{
lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3248_; 
lean_inc(v_l_3017_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
lean_inc(v_size_3014_);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; lean_object* v_unused_3250_; lean_object* v_unused_3251_; lean_object* v_unused_3252_; lean_object* v_unused_3253_; 
v_unused_3249_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v_l_2834_, 2);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v_l_2834_, 1);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3253_);
v___x_3184_ = v_l_2834_;
v_isShared_3185_ = v_isSharedCheck_3248_;
goto v_resetjp_3183_;
}
else
{
lean_dec(v_l_2834_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3248_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_size_3186_; lean_object* v_size_3187_; lean_object* v_k_3188_; lean_object* v_v_3189_; lean_object* v_l_3190_; lean_object* v_r_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v_size_3186_ = lean_ctor_get(v_l_3017_, 0);
v_size_3187_ = lean_ctor_get(v_r_3018_, 0);
v_k_3188_ = lean_ctor_get(v_r_3018_, 1);
v_v_3189_ = lean_ctor_get(v_r_3018_, 2);
v_l_3190_ = lean_ctor_get(v_r_3018_, 3);
v_r_3191_ = lean_ctor_get(v_r_3018_, 4);
v___x_3192_ = lean_unsigned_to_nat(2u);
v___x_3193_ = lean_nat_mul(v___x_3192_, v_size_3186_);
v___x_3194_ = lean_nat_dec_lt(v_size_3187_, v___x_3193_);
lean_dec(v___x_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3232_; 
lean_inc(v_r_3191_);
lean_inc(v_l_3190_);
lean_inc(v_v_3189_);
lean_inc(v_k_3188_);
lean_del_object(v___x_3184_);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_r_3018_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; lean_object* v_unused_3235_; lean_object* v_unused_3236_; lean_object* v_unused_3237_; 
v_unused_3233_ = lean_ctor_get(v_r_3018_, 4);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_r_3018_, 3);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_r_3018_, 2);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_r_3018_, 1);
lean_dec(v_unused_3236_);
v_unused_3237_ = lean_ctor_get(v_r_3018_, 0);
lean_dec(v_unused_3237_);
v___x_3196_ = v_r_3018_;
v_isShared_3197_ = v_isSharedCheck_3232_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v_r_3018_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3232_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___x_3220_; lean_object* v___y_3222_; 
v___x_3198_ = lean_nat_add(v___x_3024_, v_size_3014_);
lean_dec(v_size_3014_);
v___x_3199_ = lean_nat_add(v___x_3198_, v_size_3174_);
lean_dec(v___x_3198_);
v___x_3220_ = lean_nat_add(v___x_3024_, v_size_3186_);
if (lean_obj_tag(v_l_3190_) == 0)
{
lean_object* v_size_3230_; 
v_size_3230_ = lean_ctor_get(v_l_3190_, 0);
lean_inc(v_size_3230_);
v___y_3222_ = v_size_3230_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___y_3222_ = v___x_3231_;
goto v___jp_3221_;
}
v___jp_3200_:
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3204_ = lean_nat_add(v___y_3201_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec(v___y_3201_);
lean_inc_ref(v_tree_3171_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 4, v_tree_3171_);
lean_ctor_set(v___x_3196_, 3, v_r_3191_);
lean_ctor_set(v___x_3196_, 2, v_v_3173_);
lean_ctor_set(v___x_3196_, 1, v_k_3172_);
lean_ctor_set(v___x_3196_, 0, v___x_3204_);
v___x_3206_ = v___x_3196_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_k_3172_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_v_3173_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v_r_3191_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v_tree_3171_);
v___x_3206_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
v_isSharedCheck_3213_ = !lean_is_exclusive(v_tree_3171_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; lean_object* v_unused_3215_; lean_object* v_unused_3216_; lean_object* v_unused_3217_; lean_object* v_unused_3218_; 
v_unused_3214_ = lean_ctor_get(v_tree_3171_, 4);
lean_dec(v_unused_3214_);
v_unused_3215_ = lean_ctor_get(v_tree_3171_, 3);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_tree_3171_, 2);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_tree_3171_, 1);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_tree_3171_, 0);
lean_dec(v_unused_3218_);
v___x_3208_ = v_tree_3171_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v_tree_3171_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 4, v___x_3206_);
lean_ctor_set(v___x_3208_, 3, v___y_3202_);
lean_ctor_set(v___x_3208_, 2, v_v_3189_);
lean_ctor_set(v___x_3208_, 1, v_k_3188_);
lean_ctor_set(v___x_3208_, 0, v___x_3199_);
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_k_3188_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_v_3189_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v___y_3202_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v___x_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_nat_add(v___x_3220_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec(v___x_3220_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_l_3190_);
lean_ctor_set(v___x_3168_, 3, v_l_3017_);
lean_ctor_set(v___x_3168_, 2, v_v_3016_);
lean_ctor_set(v___x_3168_, 1, v_k_3015_);
lean_ctor_set(v___x_3168_, 0, v___x_3223_);
v___x_3225_ = v___x_3168_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_l_3017_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_l_3190_);
v___x_3225_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_nat_add(v___x_3024_, v_size_3174_);
if (lean_obj_tag(v_r_3191_) == 0)
{
lean_object* v_size_3227_; 
v_size_3227_ = lean_ctor_get(v_r_3191_, 0);
lean_inc(v_size_3227_);
v___y_3201_ = v___x_3226_;
v___y_3202_ = v___x_3225_;
v___y_3203_ = v_size_3227_;
goto v___jp_3200_;
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_unsigned_to_nat(0u);
v___y_3201_ = v___x_3226_;
v___y_3202_ = v___x_3225_;
v___y_3203_ = v___x_3228_;
goto v___jp_3200_;
}
}
}
}
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3238_ = lean_nat_add(v___x_3024_, v_size_3014_);
lean_dec(v_size_3014_);
v___x_3239_ = lean_nat_add(v___x_3238_, v_size_3174_);
lean_dec(v___x_3238_);
v___x_3240_ = lean_nat_add(v___x_3024_, v_size_3174_);
v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3187_);
lean_dec(v___x_3240_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_tree_3171_);
lean_ctor_set(v___x_3168_, 3, v_r_3018_);
lean_ctor_set(v___x_3168_, 2, v_v_3173_);
lean_ctor_set(v___x_3168_, 1, v_k_3172_);
lean_ctor_set(v___x_3168_, 0, v___x_3241_);
v___x_3243_ = v___x_3168_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_k_3172_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_v_3173_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_tree_3171_);
v___x_3243_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3245_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3243_);
lean_ctor_set(v___x_3184_, 0, v___x_3239_);
v___x_3245_ = v___x_3184_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_l_3017_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3017_) == 0)
{
lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3277_; 
lean_inc_ref(v_l_3017_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
lean_inc(v_size_3014_);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; lean_object* v_unused_3279_; lean_object* v_unused_3280_; lean_object* v_unused_3281_; lean_object* v_unused_3282_; 
v_unused_3278_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3278_);
v_unused_3279_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_l_2834_, 2);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_l_2834_, 1);
lean_dec(v_unused_3281_);
v_unused_3282_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3282_);
v___x_3255_ = v_l_2834_;
v_isShared_3256_ = v_isSharedCheck_3277_;
goto v_resetjp_3254_;
}
else
{
lean_dec(v_l_2834_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3277_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
if (lean_obj_tag(v_r_3018_) == 0)
{
lean_object* v_k_3257_; lean_object* v_v_3258_; lean_object* v_size_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v_k_3257_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_k_3257_);
v_v_3258_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_v_3258_);
lean_dec_ref(v___x_3170_);
v_size_3259_ = lean_ctor_get(v_r_3018_, 0);
v___x_3260_ = lean_nat_add(v___x_3024_, v_size_3014_);
lean_dec(v_size_3014_);
v___x_3261_ = lean_nat_add(v___x_3024_, v_size_3259_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_tree_3171_);
lean_ctor_set(v___x_3168_, 3, v_r_3018_);
lean_ctor_set(v___x_3168_, 2, v_v_3258_);
lean_ctor_set(v___x_3168_, 1, v_k_3257_);
lean_ctor_set(v___x_3168_, 0, v___x_3261_);
v___x_3263_ = v___x_3168_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_k_3257_);
lean_ctor_set(v_reuseFailAlloc_3267_, 2, v_v_3258_);
lean_ctor_set(v_reuseFailAlloc_3267_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3267_, 4, v_tree_3171_);
v___x_3263_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3265_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 4, v___x_3263_);
lean_ctor_set(v___x_3255_, 0, v___x_3260_);
v___x_3265_ = v___x_3255_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_l_3017_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
else
{
lean_object* v_k_3268_; lean_object* v_v_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
lean_dec(v_size_3014_);
v_k_3268_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_k_3268_);
v_v_3269_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_v_3269_);
lean_dec_ref(v___x_3170_);
v___x_3270_ = lean_unsigned_to_nat(3u);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_r_3018_);
lean_ctor_set(v___x_3168_, 3, v_r_3018_);
lean_ctor_set(v___x_3168_, 2, v_v_3269_);
lean_ctor_set(v___x_3168_, 1, v_k_3268_);
lean_ctor_set(v___x_3168_, 0, v___x_3024_);
v___x_3272_ = v___x_3168_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_k_3268_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_v_3269_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_r_3018_);
v___x_3272_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 4, v___x_3272_);
lean_ctor_set(v___x_3255_, 0, v___x_3270_);
v___x_3274_ = v___x_3255_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v_l_3017_);
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
}
}
else
{
if (lean_obj_tag(v_r_3018_) == 0)
{
lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3307_; 
lean_inc(v_l_3017_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; 
v_unused_3308_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_l_2834_, 2);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_l_2834_, 1);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3312_);
v___x_3284_ = v_l_2834_;
v_isShared_3285_ = v_isSharedCheck_3307_;
goto v_resetjp_3283_;
}
else
{
lean_dec(v_l_2834_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3307_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_k_3286_; lean_object* v_v_3287_; lean_object* v_k_3288_; lean_object* v_v_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3303_; 
v_k_3286_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_k_3286_);
v_v_3287_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_v_3287_);
lean_dec_ref(v___x_3170_);
v_k_3288_ = lean_ctor_get(v_r_3018_, 1);
v_v_3289_ = lean_ctor_get(v_r_3018_, 2);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_r_3018_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3304_ = lean_ctor_get(v_r_3018_, 4);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_r_3018_, 3);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_r_3018_, 0);
lean_dec(v_unused_3306_);
v___x_3291_ = v_r_3018_;
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_v_3289_);
lean_inc(v_k_3288_);
lean_dec(v_r_3018_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_unsigned_to_nat(3u);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 4, v_l_3017_);
lean_ctor_set(v___x_3291_, 3, v_l_3017_);
lean_ctor_set(v___x_3291_, 2, v_v_3016_);
lean_ctor_set(v___x_3291_, 1, v_k_3015_);
lean_ctor_set(v___x_3291_, 0, v___x_3024_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_l_3017_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_l_3017_);
v___x_3295_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_l_3017_);
lean_ctor_set(v___x_3168_, 3, v_l_3017_);
lean_ctor_set(v___x_3168_, 2, v_v_3287_);
lean_ctor_set(v___x_3168_, 1, v_k_3286_);
lean_ctor_set(v___x_3168_, 0, v___x_3024_);
v___x_3297_ = v___x_3168_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3286_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3287_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_l_3017_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_l_3017_);
v___x_3297_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 4, v___x_3297_);
lean_ctor_set(v___x_3284_, 3, v___x_3295_);
lean_ctor_set(v___x_3284_, 2, v_v_3289_);
lean_ctor_set(v___x_3284_, 1, v_k_3288_);
lean_ctor_set(v___x_3284_, 0, v___x_3293_);
v___x_3299_ = v___x_3284_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
}
else
{
lean_object* v_k_3313_; lean_object* v_v_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v_k_3313_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_k_3313_);
v_v_3314_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_v_3314_);
lean_dec_ref(v___x_3170_);
v___x_3315_ = lean_unsigned_to_nat(2u);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v_r_3018_);
lean_ctor_set(v___x_3168_, 3, v_l_2834_);
lean_ctor_set(v___x_3168_, 2, v_v_3314_);
lean_ctor_set(v___x_3168_, 1, v_k_3313_);
lean_ctor_set(v___x_3168_, 0, v___x_3315_);
v___x_3317_ = v___x_3168_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_k_3313_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_v_3314_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_l_2834_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_r_3018_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
}
}
else
{
return v_l_2834_;
}
}
else
{
return v_r_2835_;
}
}
default: 
{
lean_object* v_impl_3325_; lean_object* v___x_3326_; 
v_impl_3325_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2830_, v_r_2835_);
v___x_3326_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3325_) == 0)
{
if (lean_obj_tag(v_l_2834_) == 0)
{
lean_object* v_size_3327_; lean_object* v_size_3328_; lean_object* v_k_3329_; lean_object* v_v_3330_; lean_object* v_l_3331_; lean_object* v_r_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v_size_3327_ = lean_ctor_get(v_impl_3325_, 0);
v_size_3328_ = lean_ctor_get(v_l_2834_, 0);
v_k_3329_ = lean_ctor_get(v_l_2834_, 1);
v_v_3330_ = lean_ctor_get(v_l_2834_, 2);
v_l_3331_ = lean_ctor_get(v_l_2834_, 3);
v_r_3332_ = lean_ctor_get(v_l_2834_, 4);
lean_inc(v_r_3332_);
v___x_3333_ = lean_unsigned_to_nat(3u);
v___x_3334_ = lean_nat_mul(v___x_3333_, v_size_3327_);
v___x_3335_ = lean_nat_dec_lt(v___x_3334_, v_size_3328_);
lean_dec(v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_dec(v_r_3332_);
v___x_3336_ = lean_nat_add(v___x_3326_, v_size_3328_);
v___x_3337_ = lean_nat_add(v___x_3336_, v_size_3327_);
lean_dec(v___x_3336_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_impl_3325_);
lean_ctor_set(v___x_2837_, 0, v___x_3337_);
v___x_3339_ = v___x_2837_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_l_2834_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_impl_3325_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3406_; 
lean_inc(v_l_3331_);
lean_inc(v_v_3330_);
lean_inc(v_k_3329_);
lean_inc(v_size_3328_);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; 
v_unused_3407_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_l_2834_, 2);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_l_2834_, 1);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3411_);
v___x_3342_ = v_l_2834_;
v_isShared_3343_ = v_isSharedCheck_3406_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_l_2834_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3406_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_size_3344_; lean_object* v_size_3345_; lean_object* v_k_3346_; lean_object* v_v_3347_; lean_object* v_l_3348_; lean_object* v_r_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_size_3344_ = lean_ctor_get(v_l_3331_, 0);
v_size_3345_ = lean_ctor_get(v_r_3332_, 0);
v_k_3346_ = lean_ctor_get(v_r_3332_, 1);
v_v_3347_ = lean_ctor_get(v_r_3332_, 2);
v_l_3348_ = lean_ctor_get(v_r_3332_, 3);
v_r_3349_ = lean_ctor_get(v_r_3332_, 4);
v___x_3350_ = lean_unsigned_to_nat(2u);
v___x_3351_ = lean_nat_mul(v___x_3350_, v_size_3344_);
v___x_3352_ = lean_nat_dec_lt(v_size_3345_, v___x_3351_);
lean_dec(v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3381_; 
lean_inc(v_r_3349_);
lean_inc(v_l_3348_);
lean_inc(v_v_3347_);
lean_inc(v_k_3346_);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_r_3332_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; lean_object* v_unused_3386_; 
v_unused_3382_ = lean_ctor_get(v_r_3332_, 4);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_r_3332_, 3);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_r_3332_, 2);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_r_3332_, 1);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_r_3332_, 0);
lean_dec(v_unused_3386_);
v___x_3354_ = v_r_3332_;
v_isShared_3355_ = v_isSharedCheck_3381_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v_r_3332_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3381_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___x_3369_; lean_object* v___y_3371_; 
v___x_3356_ = lean_nat_add(v___x_3326_, v_size_3328_);
lean_dec(v_size_3328_);
v___x_3357_ = lean_nat_add(v___x_3356_, v_size_3327_);
lean_dec(v___x_3356_);
v___x_3369_ = lean_nat_add(v___x_3326_, v_size_3344_);
if (lean_obj_tag(v_l_3348_) == 0)
{
lean_object* v_size_3379_; 
v_size_3379_ = lean_ctor_get(v_l_3348_, 0);
lean_inc(v_size_3379_);
v___y_3371_ = v_size_3379_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_unsigned_to_nat(0u);
v___y_3371_ = v___x_3380_;
goto v___jp_3370_;
}
v___jp_3358_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = lean_nat_add(v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 4, v_impl_3325_);
lean_ctor_set(v___x_3354_, 3, v_r_3349_);
lean_ctor_set(v___x_3354_, 2, v_v_2833_);
lean_ctor_set(v___x_3354_, 1, v_k_2832_);
lean_ctor_set(v___x_3354_, 0, v___x_3362_);
v___x_3364_ = v___x_3354_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v_impl_3325_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v___x_3364_);
lean_ctor_set(v___x_3342_, 3, v___y_3359_);
lean_ctor_set(v___x_3342_, 2, v_v_3347_);
lean_ctor_set(v___x_3342_, 1, v_k_3346_);
lean_ctor_set(v___x_3342_, 0, v___x_3357_);
v___x_3366_ = v___x_3342_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v___y_3359_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
v___jp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_nat_add(v___x_3369_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec(v___x_3369_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_l_3348_);
lean_ctor_set(v___x_2837_, 3, v_l_3331_);
lean_ctor_set(v___x_2837_, 2, v_v_3330_);
lean_ctor_set(v___x_2837_, 1, v_k_3329_);
lean_ctor_set(v___x_2837_, 0, v___x_3372_);
v___x_3374_ = v___x_2837_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3329_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3330_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_l_3348_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_nat_add(v___x_3326_, v_size_3327_);
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_size_3376_; 
v_size_3376_ = lean_ctor_get(v_r_3349_, 0);
lean_inc(v_size_3376_);
v___y_3359_ = v___x_3374_;
v___y_3360_ = v___x_3375_;
v___y_3361_ = v_size_3376_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___y_3359_ = v___x_3374_;
v___y_3360_ = v___x_3375_;
v___y_3361_ = v___x_3377_;
goto v___jp_3358_;
}
}
}
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
lean_del_object(v___x_2837_);
v___x_3387_ = lean_nat_add(v___x_3326_, v_size_3328_);
lean_dec(v_size_3328_);
v___x_3388_ = lean_nat_add(v___x_3387_, v_size_3327_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_nat_add(v___x_3326_, v_size_3327_);
v___x_3390_ = lean_nat_add(v___x_3389_, v_size_3345_);
lean_dec(v___x_3389_);
lean_inc_ref(v_impl_3325_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v_impl_3325_);
lean_ctor_set(v___x_3342_, 3, v_r_3332_);
lean_ctor_set(v___x_3342_, 2, v_v_2833_);
lean_ctor_set(v___x_3342_, 1, v_k_2832_);
lean_ctor_set(v___x_3342_, 0, v___x_3390_);
v___x_3392_ = v___x_3342_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v_r_3332_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v_impl_3325_);
v___x_3392_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v_isSharedCheck_3399_ = !lean_is_exclusive(v_impl_3325_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; 
v_unused_3400_ = lean_ctor_get(v_impl_3325_, 4);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_impl_3325_, 3);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_impl_3325_, 2);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_impl_3325_, 1);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_impl_3325_, 0);
lean_dec(v_unused_3404_);
v___x_3394_ = v_impl_3325_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_dec(v_impl_3325_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 4, v___x_3392_);
lean_ctor_set(v___x_3394_, 3, v_l_3331_);
lean_ctor_set(v___x_3394_, 2, v_v_3330_);
lean_ctor_set(v___x_3394_, 1, v_k_3329_);
lean_ctor_set(v___x_3394_, 0, v___x_3388_);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_k_3329_);
lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_v_3330_);
lean_ctor_set(v_reuseFailAlloc_3398_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3398_, 4, v___x_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v_size_3412_ = lean_ctor_get(v_impl_3325_, 0);
v___x_3413_ = lean_nat_add(v___x_3326_, v_size_3412_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_impl_3325_);
lean_ctor_set(v___x_2837_, 0, v___x_3413_);
v___x_3415_ = v___x_2837_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_l_2834_);
lean_ctor_set(v_reuseFailAlloc_3416_, 4, v_impl_3325_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
if (lean_obj_tag(v_l_2834_) == 0)
{
lean_object* v_l_3417_; 
v_l_3417_ = lean_ctor_get(v_l_2834_, 3);
if (lean_obj_tag(v_l_3417_) == 0)
{
lean_object* v_r_3418_; 
lean_inc_ref(v_l_3417_);
v_r_3418_ = lean_ctor_get(v_l_2834_, 4);
lean_inc(v_r_3418_);
if (lean_obj_tag(v_r_3418_) == 0)
{
lean_object* v_size_3419_; lean_object* v_k_3420_; lean_object* v_v_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3434_; 
v_size_3419_ = lean_ctor_get(v_l_2834_, 0);
v_k_3420_ = lean_ctor_get(v_l_2834_, 1);
v_v_3421_ = lean_ctor_get(v_l_2834_, 2);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; lean_object* v_unused_3436_; 
v_unused_3435_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3436_);
v___x_3423_ = v_l_2834_;
v_isShared_3424_ = v_isSharedCheck_3434_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_v_3421_);
lean_inc(v_k_3420_);
lean_inc(v_size_3419_);
lean_dec(v_l_2834_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3434_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_size_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v_size_3425_ = lean_ctor_get(v_r_3418_, 0);
v___x_3426_ = lean_nat_add(v___x_3326_, v_size_3419_);
lean_dec(v_size_3419_);
v___x_3427_ = lean_nat_add(v___x_3326_, v_size_3425_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 4, v_impl_3325_);
lean_ctor_set(v___x_3423_, 3, v_r_3418_);
lean_ctor_set(v___x_3423_, 2, v_v_2833_);
lean_ctor_set(v___x_3423_, 1, v_k_2832_);
lean_ctor_set(v___x_3423_, 0, v___x_3427_);
v___x_3429_ = v___x_3423_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v_r_3418_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v_impl_3325_);
v___x_3429_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v___x_3429_);
lean_ctor_set(v___x_2837_, 3, v_l_3417_);
lean_ctor_set(v___x_2837_, 2, v_v_3421_);
lean_ctor_set(v___x_2837_, 1, v_k_3420_);
lean_ctor_set(v___x_2837_, 0, v___x_3426_);
v___x_3431_ = v___x_2837_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_k_3420_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_v_3421_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_l_3417_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_k_3437_; lean_object* v_v_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3449_; 
v_k_3437_ = lean_ctor_get(v_l_2834_, 1);
v_v_3438_ = lean_ctor_get(v_l_2834_, 2);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; lean_object* v_unused_3451_; lean_object* v_unused_3452_; 
v_unused_3450_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3452_);
v___x_3440_ = v_l_2834_;
v_isShared_3441_ = v_isSharedCheck_3449_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_v_3438_);
lean_inc(v_k_3437_);
lean_dec(v_l_2834_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3449_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_unsigned_to_nat(3u);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 3, v_r_3418_);
lean_ctor_set(v___x_3440_, 2, v_v_2833_);
lean_ctor_set(v___x_3440_, 1, v_k_2832_);
lean_ctor_set(v___x_3440_, 0, v___x_3326_);
v___x_3444_ = v___x_3440_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_r_3418_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_r_3418_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v___x_3444_);
lean_ctor_set(v___x_2837_, 3, v_l_3417_);
lean_ctor_set(v___x_2837_, 2, v_v_3438_);
lean_ctor_set(v___x_2837_, 1, v_k_3437_);
lean_ctor_set(v___x_2837_, 0, v___x_3442_);
v___x_3446_ = v___x_2837_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_3437_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_3438_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_l_3417_);
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
else
{
lean_object* v_r_3453_; 
v_r_3453_ = lean_ctor_get(v_l_2834_, 4);
lean_inc(v_r_3453_);
if (lean_obj_tag(v_r_3453_) == 0)
{
lean_object* v_k_3454_; lean_object* v_v_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3478_; 
lean_inc(v_l_3417_);
v_k_3454_ = lean_ctor_get(v_l_2834_, 1);
v_v_3455_ = lean_ctor_get(v_l_2834_, 2);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_l_2834_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; lean_object* v_unused_3480_; lean_object* v_unused_3481_; 
v_unused_3479_ = lean_ctor_get(v_l_2834_, 4);
lean_dec(v_unused_3479_);
v_unused_3480_ = lean_ctor_get(v_l_2834_, 3);
lean_dec(v_unused_3480_);
v_unused_3481_ = lean_ctor_get(v_l_2834_, 0);
lean_dec(v_unused_3481_);
v___x_3457_ = v_l_2834_;
v_isShared_3458_ = v_isSharedCheck_3478_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_v_3455_);
lean_inc(v_k_3454_);
lean_dec(v_l_2834_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3478_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_k_3459_; lean_object* v_v_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3474_; 
v_k_3459_ = lean_ctor_get(v_r_3453_, 1);
v_v_3460_ = lean_ctor_get(v_r_3453_, 2);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_r_3453_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; lean_object* v_unused_3476_; lean_object* v_unused_3477_; 
v_unused_3475_ = lean_ctor_get(v_r_3453_, 4);
lean_dec(v_unused_3475_);
v_unused_3476_ = lean_ctor_get(v_r_3453_, 3);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_r_3453_, 0);
lean_dec(v_unused_3477_);
v___x_3462_ = v_r_3453_;
v_isShared_3463_ = v_isSharedCheck_3474_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_v_3460_);
lean_inc(v_k_3459_);
lean_dec(v_r_3453_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3474_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3464_ = lean_unsigned_to_nat(3u);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 4, v_l_3417_);
lean_ctor_set(v___x_3462_, 3, v_l_3417_);
lean_ctor_set(v___x_3462_, 2, v_v_3455_);
lean_ctor_set(v___x_3462_, 1, v_k_3454_);
lean_ctor_set(v___x_3462_, 0, v___x_3326_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_3454_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_3455_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v_l_3417_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_l_3417_);
v___x_3466_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 4, v_l_3417_);
lean_ctor_set(v___x_3457_, 2, v_v_2833_);
lean_ctor_set(v___x_3457_, 1, v_k_2832_);
lean_ctor_set(v___x_3457_, 0, v___x_3326_);
v___x_3468_ = v___x_3457_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3472_, 3, v_l_3417_);
lean_ctor_set(v_reuseFailAlloc_3472_, 4, v_l_3417_);
v___x_3468_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v___x_3468_);
lean_ctor_set(v___x_2837_, 3, v___x_3466_);
lean_ctor_set(v___x_2837_, 2, v_v_3460_);
lean_ctor_set(v___x_2837_, 1, v_k_3459_);
lean_ctor_set(v___x_2837_, 0, v___x_3464_);
v___x_3470_ = v___x_2837_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_k_3459_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_v_3460_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3482_ = lean_unsigned_to_nat(2u);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_r_3453_);
lean_ctor_set(v___x_2837_, 0, v___x_3482_);
v___x_3484_ = v___x_2837_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_l_2834_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_r_3453_);
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
lean_object* v___x_3487_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_l_2834_);
lean_ctor_set(v___x_2837_, 0, v___x_3326_);
v___x_3487_ = v___x_2837_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_k_2832_);
lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_v_2833_);
lean_ctor_set(v_reuseFailAlloc_3488_, 3, v_l_2834_);
lean_ctor_set(v_reuseFailAlloc_3488_, 4, v_l_2834_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
}
}
else
{
return v_t_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3491_, lean_object* v_t_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3491_, v_t_3492_);
lean_dec(v_k_3491_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3494_, lean_object* v_ps_3495_){
_start:
{
lean_object* v_importedEntries_3496_; lean_object* v_state_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3505_; 
v_importedEntries_3496_ = lean_ctor_get(v_ps_3495_, 0);
v_state_3497_ = lean_ctor_get(v_ps_3495_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_ps_3495_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3499_ = v_ps_3495_;
v_isShared_3500_ = v_isSharedCheck_3505_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_state_3497_);
lean_inc(v_importedEntries_3496_);
lean_dec(v_ps_3495_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3505_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3501_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3494_, v_state_3497_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 1, v___x_3501_);
v___x_3503_ = v___x_3499_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_importedEntries_3496_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3506_, lean_object* v_ps_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3506_, v_ps_3507_);
lean_dec(v_declName_3506_);
return v_res_3508_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___f_3552_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___x_3575_; lean_object* v_env_3576_; lean_object* v___x_3577_; 
lean_inc(v_declName_3512_);
v___f_3552_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3552_, 0, v_declName_3512_);
v___x_3575_ = lean_st_ref_get(v___y_3518_);
v_env_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc_ref(v_env_3576_);
lean_dec(v___x_3575_);
v___x_3577_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3576_, v_declName_3512_);
lean_dec_ref(v_env_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_dec(v_declName_3512_);
v___y_3554_ = v___y_3516_;
v___y_3555_ = v___y_3518_;
goto v___jp_3553_;
}
else
{
uint8_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec_ref_known(v___x_3577_, 1);
lean_dec_ref(v___f_3552_);
v___x_3578_ = 0;
v___x_3579_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3580_ = l_Lean_MessageData_ofConstName(v_declName_3512_, v___x_3578_);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3583_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
return v___x_3584_;
}
v___jp_3520_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v_mctx_3536_; lean_object* v_zetaDeltaFVarIds_3537_; lean_object* v_postponed_3538_; lean_object* v_diag_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3550_; 
v___x_3532_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_3533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3533_, 0, v___y_3531_);
lean_ctor_set(v___x_3533_, 1, v___y_3529_);
lean_ctor_set(v___x_3533_, 2, v___y_3525_);
lean_ctor_set(v___x_3533_, 3, v___y_3523_);
lean_ctor_set(v___x_3533_, 4, v___y_3528_);
lean_ctor_set(v___x_3533_, 5, v___x_3532_);
lean_ctor_set(v___x_3533_, 6, v___y_3521_);
lean_ctor_set(v___x_3533_, 7, v___y_3530_);
lean_ctor_set(v___x_3533_, 8, v___y_3526_);
lean_ctor_set(v___x_3533_, 9, v___y_3527_);
v___x_3534_ = lean_st_ref_put(v___y_3522_, v___x_3533_);
v___x_3535_ = lean_st_ref_take(v___y_3524_);
v_mctx_3536_ = lean_ctor_get(v___x_3535_, 0);
v_zetaDeltaFVarIds_3537_ = lean_ctor_get(v___x_3535_, 2);
v_postponed_3538_ = lean_ctor_get(v___x_3535_, 3);
v_diag_3539_ = lean_ctor_get(v___x_3535_, 4);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; 
v_unused_3551_ = lean_ctor_get(v___x_3535_, 1);
lean_dec(v_unused_3551_);
v___x_3541_ = v___x_3535_;
v_isShared_3542_ = v_isSharedCheck_3550_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_diag_3539_);
lean_inc(v_postponed_3538_);
lean_inc(v_zetaDeltaFVarIds_3537_);
lean_inc(v_mctx_3536_);
lean_dec(v___x_3535_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3550_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v___x_3544_);
v___x_3546_ = v___x_3541_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_mctx_3536_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3549_, 2, v_zetaDeltaFVarIds_3537_);
lean_ctor_set(v_reuseFailAlloc_3549_, 3, v_postponed_3538_);
lean_ctor_set(v_reuseFailAlloc_3549_, 4, v_diag_3539_);
v___x_3546_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_st_ref_put(v___y_3524_, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3543_);
return v___x_3548_;
}
}
}
v___jp_3553_:
{
lean_object* v___x_3556_; lean_object* v_env_3557_; lean_object* v_nextMacroScope_3558_; lean_object* v_ngen_3559_; lean_object* v_auxDeclNGen_3560_; lean_object* v_traceState_3561_; lean_object* v_recordedDeps_3562_; lean_object* v_messages_3563_; lean_object* v_infoState_3564_; lean_object* v_snapshotTasks_3565_; lean_object* v___x_3566_; lean_object* v_toEnvExtension_3567_; uint8_t v_logWrites_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3556_ = lean_st_ref_take(v___y_3555_);
v_env_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc_ref(v_env_3557_);
v_nextMacroScope_3558_ = lean_ctor_get(v___x_3556_, 1);
lean_inc(v_nextMacroScope_3558_);
v_ngen_3559_ = lean_ctor_get(v___x_3556_, 2);
lean_inc_ref(v_ngen_3559_);
v_auxDeclNGen_3560_ = lean_ctor_get(v___x_3556_, 3);
lean_inc_ref(v_auxDeclNGen_3560_);
v_traceState_3561_ = lean_ctor_get(v___x_3556_, 4);
lean_inc_ref(v_traceState_3561_);
v_recordedDeps_3562_ = lean_ctor_get(v___x_3556_, 6);
lean_inc_ref(v_recordedDeps_3562_);
v_messages_3563_ = lean_ctor_get(v___x_3556_, 7);
lean_inc_ref(v_messages_3563_);
v_infoState_3564_ = lean_ctor_get(v___x_3556_, 8);
lean_inc_ref(v_infoState_3564_);
v_snapshotTasks_3565_ = lean_ctor_get(v___x_3556_, 9);
lean_inc_ref(v_snapshotTasks_3565_);
lean_dec(v___x_3556_);
v___x_3566_ = l_Lean_docStringExt;
v_toEnvExtension_3567_ = lean_ctor_get(v___x_3566_, 0);
v_logWrites_3568_ = lean_ctor_get_uint8(v_toEnvExtension_3567_, sizeof(void*)*6);
v___x_3569_ = lean_box(2);
v___x_3570_ = lean_box(0);
v___x_3571_ = 1;
if (v_logWrites_3568_ == 0)
{
lean_object* v___x_3572_; 
lean_inc_ref(v_toEnvExtension_3567_);
v___x_3572_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3567_, v_env_3557_, v___f_3552_, v___x_3569_, v___x_3570_, v___x_3571_);
v___y_3521_ = v_recordedDeps_3562_;
v___y_3522_ = v___y_3555_;
v___y_3523_ = v_auxDeclNGen_3560_;
v___y_3524_ = v___y_3554_;
v___y_3525_ = v_ngen_3559_;
v___y_3526_ = v_infoState_3564_;
v___y_3527_ = v_snapshotTasks_3565_;
v___y_3528_ = v_traceState_3561_;
v___y_3529_ = v_nextMacroScope_3558_;
v___y_3530_ = v_messages_3563_;
v___y_3531_ = v___x_3572_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_inc_ref_n(v_toEnvExtension_3567_, 2);
v___x_3573_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3567_, v_env_3557_);
lean_dec_ref(v_env_3557_);
v___x_3574_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3567_, v___x_3573_, v___f_3552_, v___x_3569_, v___x_3570_, v___x_3571_);
v___y_3521_ = v_recordedDeps_3562_;
v___y_3522_ = v___y_3555_;
v___y_3523_ = v_auxDeclNGen_3560_;
v___y_3524_ = v___y_3554_;
v___y_3525_ = v_ngen_3559_;
v___y_3526_ = v_infoState_3564_;
v___y_3527_ = v_snapshotTasks_3565_;
v___y_3528_ = v_traceState_3561_;
v___y_3529_ = v_nextMacroScope_3558_;
v___y_3530_ = v_messages_3563_;
v___y_3531_ = v___x_3574_;
goto v___jp_3520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
return v_res_3593_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3596_ = l_Lean_stringToMessageData(v___x_3595_);
return v___x_3596_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
return v___x_3599_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3602_ = l_Lean_stringToMessageData(v___x_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3605_ = l_Lean_stringToMessageData(v___x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3614_; lean_object* v_env_3615_; lean_object* v_ref_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3614_ = lean_st_ref_get(v_a_3612_);
v_env_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc_ref(v_env_3615_);
lean_dec(v___x_3614_);
v_ref_3616_ = lean_ctor_get(v_a_3611_, 2);
v___x_3617_ = 1;
lean_inc(v_declName_3606_);
v___x_3618_ = l_Lean_findInternalDocString_x3f(v_env_3615_, v_declName_3606_, v___x_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
if (lean_obj_tag(v_a_3619_) == 1)
{
lean_object* v_val_3620_; 
v_val_3620_ = lean_ctor_get(v_a_3619_, 0);
lean_inc(v_val_3620_);
lean_dec_ref_known(v_a_3619_, 1);
if (lean_obj_tag(v_val_3620_) == 0)
{
lean_object* v_val_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3642_; 
v_val_3621_ = lean_ctor_get(v_val_3620_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_val_3620_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3623_ = v_val_3620_;
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_val_3621_);
lean_dec(v_val_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_removeBuiltinDocString(v_declName_3606_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref_known(v___x_3625_, 1);
lean_del_object(v___x_3623_);
lean_inc(v_declName_3606_);
v___x_3626_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref_known(v___x_3626_, 1);
v___x_3627_ = l_Lean_addVersoDocStringFromString(v_declName_3606_, v_val_3621_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
return v___x_3627_;
}
else
{
lean_dec(v_val_3621_);
lean_dec(v_declName_3606_);
return v___x_3626_;
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_val_3621_);
lean_dec(v_declName_3606_);
v_a_3628_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3630_ = v___x_3625_;
v_isShared_3631_ = v_isSharedCheck_3641_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3625_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3641_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = lean_io_error_to_string(v_a_3628_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 3);
lean_ctor_set(v___x_3623_, 0, v___x_3632_);
v___x_3634_ = v___x_3623_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3635_ = l_Lean_MessageData_ofFormat(v___x_3634_);
lean_inc(v_ref_3616_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v_ref_3616_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3636_);
v___x_3638_ = v___x_3630_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
}
else
{
lean_object* v___x_3643_; uint8_t v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec(v_val_3620_);
v___x_3643_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3644_ = 0;
v___x_3645_ = l_Lean_MessageData_ofConstName(v_declName_3606_, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3643_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3648_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
return v___x_3649_;
}
}
else
{
lean_object* v___x_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec(v_a_3619_);
v___x_3650_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3651_ = 0;
v___x_3652_ = l_Lean_MessageData_ofConstName(v_declName_3606_, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3650_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3655_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
return v___x_3656_;
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v_declName_3606_);
v_a_3657_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3659_ = v___x_3618_;
v_isShared_3660_ = v_isSharedCheck_3668_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3618_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3668_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3661_ = lean_io_error_to_string(v_a_3657_);
v___x_3662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
v___x_3663_ = l_Lean_MessageData_ofFormat(v___x_3662_);
lean_inc(v_ref_3616_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_ref_3616_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v___x_3664_);
v___x_3666_ = v___x_3659_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_makeDocStringVerso(v_declName_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
lean_dec(v_a_3675_);
lean_dec_ref(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3672_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3678_, lean_object* v_k_3679_, lean_object* v_t_3680_, lean_object* v_h_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3679_, v_t_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3683_, lean_object* v_k_3684_, lean_object* v_t_3685_, lean_object* v_h_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3683_, v_k_3684_, v_t_3685_, v_h_3686_);
lean_dec(v_k_3684_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3688_, lean_object* v_binders_3689_, lean_object* v_docComment_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
uint8_t v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = l_Lean_isVersoDocComment(v_docComment_3690_);
v___x_3699_ = l_Lean_addDocStringOf(v___x_3698_, v_declName_3688_, v_binders_3689_, v_docComment_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3700_, lean_object* v_binders_3701_, lean_object* v_docComment_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_addDocString(v_declName_3700_, v_binders_3701_, v_docComment_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3711_, lean_object* v_binders_3712_, lean_object* v_docString_x3f_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3713_) == 0)
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
lean_dec(v_binders_3712_);
lean_dec(v_declName_3711_);
v___x_3721_ = lean_box(0);
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
else
{
lean_object* v_val_3723_; lean_object* v___x_3724_; 
v_val_3723_ = lean_ctor_get(v_docString_x3f_3713_, 0);
lean_inc(v_val_3723_);
lean_dec_ref_known(v_docString_x3f_3713_, 1);
v___x_3724_ = l_Lean_addDocString(v_declName_3711_, v_binders_3712_, v_val_3723_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3725_, lean_object* v_binders_3726_, lean_object* v_docString_x3f_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_addDocString_x27(v_declName_3725_, v_binders_3726_, v_docString_x3f_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v___x_3740_; lean_object* v_nextMacroScope_3741_; lean_object* v_ngen_3742_; lean_object* v_auxDeclNGen_3743_; lean_object* v_traceState_3744_; lean_object* v_recordedDeps_3745_; lean_object* v_messages_3746_; lean_object* v_infoState_3747_; lean_object* v_snapshotTasks_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3774_; 
v___x_3740_ = lean_st_ref_take(v___y_3738_);
v_nextMacroScope_3741_ = lean_ctor_get(v___x_3740_, 1);
v_ngen_3742_ = lean_ctor_get(v___x_3740_, 2);
v_auxDeclNGen_3743_ = lean_ctor_get(v___x_3740_, 3);
v_traceState_3744_ = lean_ctor_get(v___x_3740_, 4);
v_recordedDeps_3745_ = lean_ctor_get(v___x_3740_, 6);
v_messages_3746_ = lean_ctor_get(v___x_3740_, 7);
v_infoState_3747_ = lean_ctor_get(v___x_3740_, 8);
v_snapshotTasks_3748_ = lean_ctor_get(v___x_3740_, 9);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; lean_object* v_unused_3776_; 
v_unused_3775_ = lean_ctor_get(v___x_3740_, 5);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v___x_3740_, 0);
lean_dec(v_unused_3776_);
v___x_3750_ = v___x_3740_;
v_isShared_3751_ = v_isSharedCheck_3774_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_snapshotTasks_3748_);
lean_inc(v_infoState_3747_);
lean_inc(v_messages_3746_);
lean_inc(v_recordedDeps_3745_);
lean_inc(v_traceState_3744_);
lean_inc(v_auxDeclNGen_3743_);
lean_inc(v_ngen_3742_);
lean_inc(v_nextMacroScope_3741_);
lean_dec(v___x_3740_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3774_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3752_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 5, v___x_3752_);
lean_ctor_set(v___x_3750_, 0, v_env_3736_);
v___x_3754_ = v___x_3750_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_env_3736_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_nextMacroScope_3741_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_ngen_3742_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_auxDeclNGen_3743_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_traceState_3744_);
lean_ctor_set(v_reuseFailAlloc_3773_, 5, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3773_, 6, v_recordedDeps_3745_);
lean_ctor_set(v_reuseFailAlloc_3773_, 7, v_messages_3746_);
lean_ctor_set(v_reuseFailAlloc_3773_, 8, v_infoState_3747_);
lean_ctor_set(v_reuseFailAlloc_3773_, 9, v_snapshotTasks_3748_);
v___x_3754_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v_mctx_3757_; lean_object* v_zetaDeltaFVarIds_3758_; lean_object* v_postponed_3759_; lean_object* v_diag_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3771_; 
v___x_3755_ = lean_st_ref_put(v___y_3738_, v___x_3754_);
v___x_3756_ = lean_st_ref_take(v___y_3737_);
v_mctx_3757_ = lean_ctor_get(v___x_3756_, 0);
v_zetaDeltaFVarIds_3758_ = lean_ctor_get(v___x_3756_, 2);
v_postponed_3759_ = lean_ctor_get(v___x_3756_, 3);
v_diag_3760_ = lean_ctor_get(v___x_3756_, 4);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___x_3756_, 1);
lean_dec(v_unused_3772_);
v___x_3762_ = v___x_3756_;
v_isShared_3763_ = v_isSharedCheck_3771_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_diag_3760_);
lean_inc(v_postponed_3759_);
lean_inc(v_zetaDeltaFVarIds_3758_);
lean_inc(v_mctx_3757_);
lean_dec(v___x_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3771_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3764_ = lean_box(0);
v___x_3765_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 1, v___x_3765_);
v___x_3767_ = v___x_3762_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_mctx_3757_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_zetaDeltaFVarIds_3758_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_postponed_3759_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_diag_3760_);
v___x_3767_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = lean_st_ref_put(v___y_3737_, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3764_);
return v___x_3769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec(v___y_3778_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3782_, uint8_t v___x_3783_, lean_object* v_as_3784_, size_t v_i_3785_, size_t v_stop_3786_, lean_object* v_b_3787_){
_start:
{
lean_object* v___y_3789_; uint8_t v___x_3793_; 
v___x_3793_ = lean_usize_dec_eq(v_i_3785_, v_stop_3786_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v_index_3795_; lean_object* v_sourceString_3796_; lean_object* v_imports_3797_; lean_object* v_currNamespace_3798_; lean_object* v_openDecls_3799_; lean_object* v_options_3800_; lean_object* v_check_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3818_; 
v___x_3794_ = lean_array_uget(v_as_3784_, v_i_3785_);
v_index_3795_ = lean_ctor_get(v___x_3794_, 1);
v_sourceString_3796_ = lean_ctor_get(v___x_3794_, 2);
v_imports_3797_ = lean_ctor_get(v___x_3794_, 3);
v_currNamespace_3798_ = lean_ctor_get(v___x_3794_, 4);
v_openDecls_3799_ = lean_ctor_get(v___x_3794_, 5);
v_options_3800_ = lean_ctor_get(v___x_3794_, 6);
v_check_3801_ = lean_ctor_get(v___x_3794_, 7);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v___x_3794_, 0);
lean_dec(v_unused_3819_);
v___x_3803_ = v___x_3794_;
v_isShared_3804_ = v_isSharedCheck_3818_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_check_3801_);
lean_inc(v_options_3800_);
lean_inc(v_openDecls_3799_);
lean_inc(v_currNamespace_3798_);
lean_inc(v_imports_3797_);
lean_inc(v_sourceString_3796_);
lean_inc(v_index_3795_);
lean_dec(v___x_3794_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3818_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v_toEnvExtension_3806_; lean_object* v_asyncMode_3807_; uint8_t v_logWrites_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3805_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3806_ = lean_ctor_get(v___x_3805_, 0);
v_asyncMode_3807_ = lean_ctor_get(v_toEnvExtension_3806_, 2);
v_logWrites_3808_ = lean_ctor_get_uint8(v_toEnvExtension_3806_, sizeof(void*)*6);
lean_inc(v_n_3782_);
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v_n_3782_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3809_);
v___x_3811_ = v___x_3803_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_index_3795_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v_sourceString_3796_);
lean_ctor_set(v_reuseFailAlloc_3817_, 3, v_imports_3797_);
lean_ctor_set(v_reuseFailAlloc_3817_, 4, v_currNamespace_3798_);
lean_ctor_set(v_reuseFailAlloc_3817_, 5, v_openDecls_3799_);
lean_ctor_set(v_reuseFailAlloc_3817_, 6, v_options_3800_);
lean_ctor_set(v_reuseFailAlloc_3817_, 7, v_check_3801_);
v___x_3811_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___f_3812_; lean_object* v___x_3813_; 
v___f_3812_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_3812_, 0, v___x_3805_);
lean_closure_set(v___f_3812_, 1, v___x_3811_);
v___x_3813_ = lean_box(0);
if (v_logWrites_3808_ == 0)
{
lean_object* v___x_3814_; 
lean_inc_ref(v_toEnvExtension_3806_);
v___x_3814_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3806_, v_b_3787_, v___f_3812_, v_asyncMode_3807_, v___x_3813_, v___x_3783_);
v___y_3789_ = v___x_3814_;
goto v___jp_3788_;
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_inc_ref_n(v_toEnvExtension_3806_, 2);
v___x_3815_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3806_, v_b_3787_);
lean_dec_ref(v_b_3787_);
v___x_3816_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3806_, v___x_3815_, v___f_3812_, v_asyncMode_3807_, v___x_3813_, v___x_3783_);
v___y_3789_ = v___x_3816_;
goto v___jp_3788_;
}
}
}
}
else
{
lean_dec(v_n_3782_);
return v_b_3787_;
}
v___jp_3788_:
{
size_t v___x_3790_; size_t v___x_3791_; 
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3785_, v___x_3790_);
v_i_3785_ = v___x_3791_;
v_b_3787_ = v___y_3789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3820_, lean_object* v___x_3821_, lean_object* v_as_3822_, lean_object* v_i_3823_, lean_object* v_stop_3824_, lean_object* v_b_3825_){
_start:
{
uint8_t v___x_1351__boxed_3826_; size_t v_i_boxed_3827_; size_t v_stop_boxed_3828_; lean_object* v_res_3829_; 
v___x_1351__boxed_3826_ = lean_unbox(v___x_3821_);
v_i_boxed_3827_ = lean_unbox_usize(v_i_3823_);
lean_dec(v_i_3823_);
v_stop_boxed_3828_ = lean_unbox_usize(v_stop_3824_);
lean_dec(v_stop_3824_);
v_res_3829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3820_, v___x_1351__boxed_3826_, v_as_3822_, v_i_boxed_3827_, v_stop_boxed_3828_, v_b_3825_);
lean_dec_ref(v_as_3822_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3830_, lean_object* v_deferred_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v___x_3839_; lean_object* v_env_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3839_ = lean_st_ref_get(v___y_3837_);
v_env_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc_ref(v_env_3840_);
lean_dec(v___x_3839_);
v___x_3841_ = l_Lean_getMainModuleDoc(v_env_3840_);
v___x_3842_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3841_);
lean_dec_ref(v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec_ref(v_docs_3830_);
v___x_3843_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3844_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3843_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3844_;
}
else
{
lean_object* v___x_3845_; lean_object* v_env_3846_; lean_object* v___x_3847_; lean_object* v_size_3848_; lean_object* v___x_3849_; lean_object* v_env_3850_; lean_object* v___x_3851_; 
v___x_3845_ = lean_st_ref_get(v___y_3837_);
v_env_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc_ref(v_env_3846_);
lean_dec(v___x_3845_);
v___x_3847_ = l_Lean_getMainVersoModuleDocs(v_env_3846_);
v_size_3848_ = lean_ctor_get(v___x_3847_, 2);
lean_inc(v_size_3848_);
lean_dec_ref(v___x_3847_);
v___x_3849_ = lean_st_ref_get(v___y_3837_);
v_env_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc_ref(v_env_3850_);
lean_dec(v___x_3849_);
v___x_3851_ = l_Lean_addVersoModuleDocSnippet(v_env_3850_, v_docs_3830_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec(v_size_3848_);
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_3854_ = l_Lean_stringToMessageData(v_a_3852_);
v___x_3855_ = l_Lean_indentD(v___x_3854_);
v___x_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3853_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3856_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3857_;
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v_a_3858_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3859_ = lean_unsigned_to_nat(0u);
v___x_3860_ = lean_array_get_size(v_deferred_3831_);
v___x_3861_ = lean_nat_dec_lt(v___x_3859_, v___x_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
lean_dec(v_size_3848_);
v___x_3862_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3858_, v___y_3835_, v___y_3837_);
return v___x_3862_;
}
else
{
size_t v___x_3863_; size_t v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3863_ = ((size_t)0ULL);
v___x_3864_ = lean_usize_of_nat(v___x_3860_);
v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3848_, v___x_3842_, v_deferred_3831_, v___x_3863_, v___x_3864_, v_a_3858_);
v___x_3866_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3865_, v___y_3835_, v___y_3837_);
return v___x_3866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3867_, lean_object* v_deferred_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3867_, v_deferred_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec_ref(v_deferred_3868_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3877_, lean_object* v_doc_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_versoModDocString(v_range_3877_, v_doc_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v_fst_3888_; lean_object* v_snd_3889_; lean_object* v___x_3890_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v_fst_3888_ = lean_ctor_get(v_a_3887_, 0);
lean_inc(v_fst_3888_);
v_snd_3889_ = lean_ctor_get(v_a_3887_, 1);
lean_inc(v_snd_3889_);
lean_dec(v_a_3887_);
v___x_3890_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3888_, v_snd_3889_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_snd_3889_);
return v___x_3890_;
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v_a_3891_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3886_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3886_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3899_, lean_object* v_doc_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_addVersoModDocString(v_range_3899_, v_doc_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_doc_3900_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3909_, v___y_3913_, v___y_3915_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
return v_res_3926_;
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
