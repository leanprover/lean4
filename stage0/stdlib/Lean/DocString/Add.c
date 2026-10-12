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
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(uint8_t v_suppressElabErrors_326_, uint8_t v___x_327_, lean_object* v_x_328_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_326_ = stack[0].m_num;
uint8_t v___x_327_ = stack[1].m_num;
lean_object* v_x_328_ = stack[2].m_obj;
uint8_t v_res_354_;
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(v_suppressElabErrors_326_, v___x_327_, v_x_328_);
stack->m_num = v_res_354_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v_as_364_, size_t v_sz_365_, size_t v_i_366_, lean_object* v_b_367_, lean_object* v___y_368_, lean_object* v___y_369_){
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
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_nat_dec_eq(v___x_363_, v___x_439_);
v___x_441_ = lean_box(v_suppressElabErrors_388_);
v___x_442_ = lean_box(v___x_440_);
v___f_443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_443_, 0, v___x_441_);
lean_closure_set(v___f_443_, 1, v___x_442_);
lean_inc(v_data_438_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_362_ = stack[0].m_obj;
lean_object* v___x_363_ = stack[1].m_obj;
lean_object* v_as_364_ = stack[2].m_obj;
size_t v_sz_365_ = stack[3].m_num;
size_t v_i_366_ = stack[4].m_num;
lean_object* v_b_367_ = stack[5].m_obj;
lean_object* v___y_368_ = stack[6].m_obj;
lean_object* v___y_369_ = stack[7].m_obj;
lean_object* v_res_448_;
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_362_, v___x_363_, v_as_364_, v_sz_365_, v_i_366_, v_b_367_, v___y_368_, v___y_369_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___boxed(lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_as_451_, lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
size_t v_sz_boxed_458_; size_t v_i_boxed_459_; lean_object* v_res_460_; 
v_sz_boxed_458_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_459_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_449_, v___x_450_, v_as_451_, v_sz_boxed_458_, v_i_boxed_459_, v_b_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_as_451_);
lean_dec(v___x_450_);
return v_res_460_;
}
}
lean_object* l_Lean_parseVersoDocStringAt(lean_object* v_openPos_461_, lean_object* v_startPos_462_, lean_object* v_endPos_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_toCold_467_; lean_object* v_fileMap_468_; lean_object* v_fileName_469_; lean_object* v_currNamespace_470_; lean_object* v_openDecls_471_; lean_object* v_source_472_; lean_object* v___y_474_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_toCold_467_ = lean_ctor_get(v_a_464_, 0);
v_fileMap_468_ = lean_ctor_get(v_toCold_467_, 1);
v_fileName_469_ = lean_ctor_get(v_toCold_467_, 0);
v_currNamespace_470_ = lean_ctor_get(v_toCold_467_, 4);
v_openDecls_471_ = lean_ctor_get(v_toCold_467_, 5);
v_source_472_ = lean_ctor_get(v_fileMap_468_, 0);
v___x_515_ = lean_string_utf8_byte_size(v_source_472_);
v___x_516_ = lean_nat_dec_le(v_endPos_463_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec(v_endPos_463_);
v___y_474_ = v___x_515_;
goto v___jp_473_;
}
else
{
v___y_474_ = v_endPos_463_;
goto v___jp_473_;
}
v___jp_473_:
{
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_475_ = lean_st_ref_get(v_a_465_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref_n(v_env_476_, 2);
lean_dec(v___x_475_);
lean_inc(v___y_474_);
lean_inc_ref_n(v_fileMap_468_, 2);
lean_inc_ref(v_fileName_469_);
lean_inc_ref(v_source_472_);
v___x_477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_477_, 0, v_source_472_);
lean_ctor_set(v___x_477_, 1, v_fileName_469_);
lean_ctor_set(v___x_477_, 2, v_fileMap_468_);
lean_ctor_set(v___x_477_, 3, v___y_474_);
v___x_478_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_464_);
lean_inc(v_openDecls_471_);
lean_inc(v_currNamespace_470_);
v___x_479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_479_, 0, v_env_476_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_ctor_set(v___x_479_, 2, v_currNamespace_470_);
lean_ctor_set(v___x_479_, 3, v_openDecls_471_);
lean_inc(v_startPos_462_);
v___x_480_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_468_, v_openPos_461_, v_startPos_462_, v___y_474_);
v___x_481_ = l_Lean_Parser_mkParserState(v_source_472_);
v___x_482_ = l_Lean_Parser_ParserState_setPos(v___x_481_, v_startPos_462_);
v___x_483_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_483_, 0, v___x_480_);
v___x_484_ = l_Lean_Parser_getTokenTable(v_env_476_);
lean_inc_ref(v___x_477_);
v___x_485_ = l_Lean_Parser_ParserFn_run(v___x_483_, v___x_477_, v___x_479_, v___x_484_, v___x_482_);
lean_inc_ref(v___x_485_);
v___x_486_ = l_Lean_Parser_ParserState_allErrors(v___x_485_);
v___x_487_ = lean_array_get_size(v___x_486_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_nat_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; size_t v_sz_491_; size_t v___x_492_; lean_object* v___x_493_; 
lean_dec_ref(v___x_485_);
v___x_490_ = lean_box(0);
v_sz_491_ = lean_array_size(v___x_486_);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_477_, v___x_487_, v___x_486_, v_sz_491_, v___x_492_, v___x_490_, v_a_464_, v_a_465_);
lean_dec_ref(v___x_486_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v___x_493_, 0);
lean_dec(v_unused_502_);
v___x_495_ = v___x_493_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_dec(v___x_493_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_a_503_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_493_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_493_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_stxStack_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec_ref(v___x_486_);
lean_dec_ref_known(v___x_477_, 4);
v_stxStack_511_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_stxStack_511_);
lean_dec_ref(v___x_485_);
v___x_512_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_511_);
lean_dec_ref(v_stxStack_511_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT void l_Lean_parseVersoDocStringAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_openPos_461_ = stack[0].m_obj;
lean_object* v_startPos_462_ = stack[1].m_obj;
lean_object* v_endPos_463_ = stack[2].m_obj;
lean_object* v_a_464_ = stack[3].m_obj;
lean_object* v_a_465_ = stack[4].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Lean_parseVersoDocStringAt(v_openPos_461_, v_startPos_462_, v_endPos_463_, v_a_464_, v_a_465_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt___boxed(lean_object* v_openPos_518_, lean_object* v_startPos_519_, lean_object* v_endPos_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_parseVersoDocStringAt(v_openPos_518_, v_startPos_519_, v_endPos_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_openPos_518_);
return v_res_524_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_525_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
lean_ctor_set(v___x_531_, 3, v___x_530_);
lean_ctor_set(v___x_531_, 4, v___x_529_);
lean_ctor_set(v___x_531_, 5, v___x_529_);
lean_ctor_set(v___x_531_, 6, v___x_529_);
lean_ctor_set(v___x_531_, 7, v___x_529_);
lean_ctor_set(v___x_531_, 8, v___x_529_);
lean_ctor_set(v___x_531_, 9, v___x_529_);
lean_ctor_set(v___x_531_, 10, v___x_529_);
lean_ctor_set(v___x_531_, 11, v___x_528_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_unsigned_to_nat(32u);
v___x_533_ = lean_mk_empty_array_with_capacity(v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_535_ = ((size_t)5ULL);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_unsigned_to_nat(32u);
v___x_538_ = lean_mk_empty_array_with_capacity(v___x_537_);
v___x_539_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3);
v___x_540_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___x_536_);
lean_ctor_set(v___x_540_, 3, v___x_536_);
lean_ctor_set_usize(v___x_540_, 4, v___x_535_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_box(1);
v___x_542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4);
v___x_543_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_542_);
lean_ctor_set(v___x_544_, 2, v___x_541_);
return v___x_544_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(lean_object* v_msgData_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; lean_object* v_toCold_550_; lean_object* v_env_551_; lean_object* v_options_552_; uint8_t v___x_553_; lean_object* v_env_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_549_ = lean_st_ref_get(v___y_547_);
v_toCold_550_ = lean_ctor_get(v___y_546_, 0);
v_env_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_env_551_);
lean_dec(v___x_549_);
v_options_552_ = lean_ctor_get(v_toCold_550_, 2);
v___x_553_ = 0;
v_env_554_ = l_Lean_Environment_setRecordingDeps(v_env_551_, v___x_553_);
v___x_555_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2);
v___x_556_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_552_);
v___x_557_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_557_, 0, v_env_554_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
lean_ctor_set(v___x_557_, 2, v___x_556_);
lean_ctor_set(v___x_557_, 3, v_options_552_);
v___x_558_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_msgData_545_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_545_ = stack[0].m_obj;
lean_object* v___y_546_ = stack[1].m_obj;
lean_object* v___y_547_ = stack[2].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msgData_545_, v___y_546_, v___y_547_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___boxed(lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msgData_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_565_;
}
}
lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(lean_object* v_msg_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_ref_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_ref_570_ = lean_ctor_get(v___y_567_, 2);
v___x_571_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msg_566_, v___y_567_, v___y_568_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_ref_570_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_ref_570_);
lean_ctor_set(v___x_576_, 1, v_a_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_566_ = stack[0].m_obj;
lean_object* v___y_567_ = stack[1].m_obj;
lean_object* v___y_568_ = stack[2].m_obj;
lean_object* v_res_581_;
v_res_581_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_566_, v___y_567_, v___y_568_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg___boxed(lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_586_;
}
}
lean_object* l_Lean_parseVersoDocString(lean_object* v_docComment_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_____x_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___x_600_; 
v___x_600_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_587_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_601_, v_a_588_, v_a_589_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_600_, 1);
v_____x_592_ = v_a_611_;
v___y_593_ = v_a_588_;
v___y_594_ = v_a_589_;
goto v___jp_591_;
}
v___jp_591_:
{
lean_object* v_snd_595_; lean_object* v_fst_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_599_; 
v_snd_595_ = lean_ctor_get(v_____x_592_, 1);
lean_inc(v_snd_595_);
v_fst_596_ = lean_ctor_get(v_____x_592_, 0);
lean_inc(v_fst_596_);
lean_dec_ref(v_____x_592_);
v_fst_597_ = lean_ctor_get(v_snd_595_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v_snd_595_, 1);
lean_inc(v_snd_598_);
lean_dec(v_snd_595_);
v___x_599_ = l_Lean_parseVersoDocStringAt(v_fst_596_, v_fst_597_, v_snd_598_, v___y_593_, v___y_594_);
lean_dec(v_fst_596_);
return v___x_599_;
}
}
}
LEAN_EXPORT void l_Lean_parseVersoDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_docComment_587_ = stack[0].m_obj;
lean_object* v_a_588_ = stack[1].m_obj;
lean_object* v_a_589_ = stack[2].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_Lean_parseVersoDocString(v_docComment_587_, v_a_588_, v_a_589_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___boxed(lean_object* v_docComment_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_parseVersoDocString(v_docComment_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_docComment_613_);
return v_res_617_;
}
}
lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_object* v_00_u03b1_618_, lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_619_ = stack[1].m_obj;
lean_object* v___y_620_ = stack[2].m_obj;
lean_object* v___y_621_ = stack[3].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_box(0), v_msg_619_, v___y_620_, v___y_621_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___boxed(lean_object* v_00_u03b1_625_, lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(v_00_u03b1_625_, v_msg_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_630_;
}
}
lean_object* l_Lean_reportVersoParseFailure(lean_object* v_view_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_____x_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_631_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_662_, v_a_632_, v_a_633_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; 
v_a_672_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_661_, 1);
v_____x_636_ = v_a_672_;
v___y_637_ = v_a_632_;
v___y_638_ = v_a_633_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v_snd_639_; lean_object* v_fst_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_snd_639_ = lean_ctor_get(v_____x_636_, 1);
lean_inc(v_snd_639_);
v_fst_640_ = lean_ctor_get(v_____x_636_, 0);
lean_inc(v_fst_640_);
lean_dec_ref(v_____x_636_);
v_fst_641_ = lean_ctor_get(v_snd_639_, 0);
lean_inc(v_fst_641_);
v_snd_642_ = lean_ctor_get(v_snd_639_, 1);
lean_inc(v_snd_642_);
lean_dec(v_snd_639_);
v___x_643_ = lean_box(0);
v___x_644_ = l_Lean_parseVersoDocStringAt(v_fst_640_, v_fst_641_, v_snd_642_, v___y_637_, v___y_638_);
lean_dec(v_fst_640_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_652_);
v___x_646_ = v___x_644_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_644_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_643_);
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_643_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
v_a_653_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_644_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_644_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_reportVersoParseFailure_0interp(lean_interpreter_value* stack)
{
lean_object* v_view_631_ = stack[0].m_obj;
lean_object* v_a_632_ = stack[1].m_obj;
lean_object* v_a_633_ = stack[2].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_reportVersoParseFailure(v_view_631_, v_a_632_, v_a_633_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_view_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_reportVersoParseFailure(v_view_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec_ref(v_view_674_);
return v_res_678_;
}
}
lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_679_, lean_object* v_declName_680_, lean_object* v_binders_681_, lean_object* v___x_682_, uint8_t v___x_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_679_) == 0)
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Doc_DocM_exec___redArg(v_declName_680_, v_binders_681_, v___x_682_, v___x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_691_;
}
else
{
lean_object* v_toCold_692_; lean_object* v_val_693_; lean_object* v_currRecDepth_694_; lean_object* v_ref_695_; uint16_t v_optionFlags_696_; uint8_t v_suppressElabErrors_697_; uint8_t v_isRecordingDeps_698_; lean_object* v_fileName_699_; lean_object* v_options_700_; lean_object* v_maxRecDepth_701_; lean_object* v_currNamespace_702_; lean_object* v_openDecls_703_; lean_object* v_initHeartbeats_704_; lean_object* v_maxHeartbeats_705_; lean_object* v_quotContext_706_; lean_object* v_currMacroScope_707_; lean_object* v_cancelTk_x3f_708_; lean_object* v_inheritedTraceOptions_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_toCold_692_ = lean_ctor_get(v___y_688_, 0);
v_val_693_ = lean_ctor_get(v_fileMap_x3f_679_, 0);
v_currRecDepth_694_ = lean_ctor_get(v___y_688_, 1);
v_ref_695_ = lean_ctor_get(v___y_688_, 2);
v_optionFlags_696_ = lean_ctor_get_uint16(v___y_688_, sizeof(void*)*3);
v_suppressElabErrors_697_ = lean_ctor_get_uint8(v___y_688_, sizeof(void*)*3 + 2);
v_isRecordingDeps_698_ = lean_ctor_get_uint8(v___y_688_, sizeof(void*)*3 + 3);
v_fileName_699_ = lean_ctor_get(v_toCold_692_, 0);
v_options_700_ = lean_ctor_get(v_toCold_692_, 2);
v_maxRecDepth_701_ = lean_ctor_get(v_toCold_692_, 3);
v_currNamespace_702_ = lean_ctor_get(v_toCold_692_, 4);
v_openDecls_703_ = lean_ctor_get(v_toCold_692_, 5);
v_initHeartbeats_704_ = lean_ctor_get(v_toCold_692_, 6);
v_maxHeartbeats_705_ = lean_ctor_get(v_toCold_692_, 7);
v_quotContext_706_ = lean_ctor_get(v_toCold_692_, 8);
v_currMacroScope_707_ = lean_ctor_get(v_toCold_692_, 9);
v_cancelTk_x3f_708_ = lean_ctor_get(v_toCold_692_, 10);
v_inheritedTraceOptions_709_ = lean_ctor_get(v_toCold_692_, 11);
lean_inc_ref(v_inheritedTraceOptions_709_);
lean_inc(v_cancelTk_x3f_708_);
lean_inc(v_currMacroScope_707_);
lean_inc(v_quotContext_706_);
lean_inc(v_maxHeartbeats_705_);
lean_inc(v_initHeartbeats_704_);
lean_inc(v_openDecls_703_);
lean_inc(v_currNamespace_702_);
lean_inc(v_maxRecDepth_701_);
lean_inc_ref(v_options_700_);
lean_inc(v_val_693_);
lean_inc_ref(v_fileName_699_);
v___x_710_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_710_, 0, v_fileName_699_);
lean_ctor_set(v___x_710_, 1, v_val_693_);
lean_ctor_set(v___x_710_, 2, v_options_700_);
lean_ctor_set(v___x_710_, 3, v_maxRecDepth_701_);
lean_ctor_set(v___x_710_, 4, v_currNamespace_702_);
lean_ctor_set(v___x_710_, 5, v_openDecls_703_);
lean_ctor_set(v___x_710_, 6, v_initHeartbeats_704_);
lean_ctor_set(v___x_710_, 7, v_maxHeartbeats_705_);
lean_ctor_set(v___x_710_, 8, v_quotContext_706_);
lean_ctor_set(v___x_710_, 9, v_currMacroScope_707_);
lean_ctor_set(v___x_710_, 10, v_cancelTk_x3f_708_);
lean_ctor_set(v___x_710_, 11, v_inheritedTraceOptions_709_);
lean_inc(v_ref_695_);
lean_inc(v_currRecDepth_694_);
v___x_711_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_currRecDepth_694_);
lean_ctor_set(v___x_711_, 2, v_ref_695_);
lean_ctor_set_uint16(v___x_711_, sizeof(void*)*3, v_optionFlags_696_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*3 + 2, v_suppressElabErrors_697_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*3 + 3, v_isRecordingDeps_698_);
v___x_712_ = l_Lean_Doc_DocM_exec___redArg(v_declName_680_, v_binders_681_, v___x_682_, v___x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___x_711_, v___y_689_);
lean_dec_ref_known(v___x_711_, 3);
return v___x_712_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_x3f_679_ = stack[0].m_obj;
lean_object* v_declName_680_ = stack[1].m_obj;
lean_object* v_binders_681_ = stack[2].m_obj;
lean_object* v___x_682_ = stack[3].m_obj;
uint8_t v___x_683_ = stack[4].m_num;
lean_object* v___y_684_ = stack[5].m_obj;
lean_object* v___y_685_ = stack[6].m_obj;
lean_object* v___y_686_ = stack[7].m_obj;
lean_object* v___y_687_ = stack[8].m_obj;
lean_object* v___y_688_ = stack[9].m_obj;
lean_object* v___y_689_ = stack[10].m_obj;
lean_object* v_res_713_;
v_res_713_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_679_, v_declName_680_, v_binders_681_, v___x_682_, v___x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_714_, lean_object* v_declName_715_, lean_object* v_binders_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v___x_9836__boxed_726_; lean_object* v_res_727_; 
v___x_9836__boxed_726_ = lean_unbox(v___x_718_);
v_res_727_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_714_, v_declName_715_, v_binders_716_, v___x_717_, v___x_9836__boxed_726_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v_fileMap_x3f_714_);
return v_res_727_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_728_, size_t v_i_729_, lean_object* v_bs_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_729_, v_sz_728_);
if (v___x_731_ == 0)
{
return v_bs_730_;
}
else
{
lean_object* v_v_732_; lean_object* v___x_733_; lean_object* v_bs_x27_734_; size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v_v_732_ = lean_array_uget(v_bs_730_, v_i_729_);
v___x_733_ = lean_unsigned_to_nat(0u);
v_bs_x27_734_ = lean_array_uset(v_bs_730_, v_i_729_, v___x_733_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_729_, v___x_735_);
v___x_737_ = lean_array_uset(v_bs_x27_734_, v_i_729_, v_v_732_);
v_i_729_ = v___x_736_;
v_bs_730_ = v___x_737_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_728_ = stack[0].m_num;
size_t v_i_729_ = stack[1].m_num;
lean_object* v_bs_730_ = stack[2].m_obj;
lean_object* v_res_739_;
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_728_, v_i_729_, v_bs_730_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_740_, lean_object* v_i_741_, lean_object* v_bs_742_){
_start:
{
size_t v_sz_boxed_743_; size_t v_i_boxed_744_; lean_object* v_res_745_; 
v_sz_boxed_743_ = lean_unbox_usize(v_sz_740_);
lean_dec(v_sz_740_);
v_i_boxed_744_ = lean_unbox_usize(v_i_741_);
lean_dec(v_i_741_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_743_, v_i_boxed_744_, v_bs_742_);
return v_res_745_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_746_, lean_object* v_opt_747_){
_start:
{
lean_object* v_name_748_; lean_object* v_defValue_749_; lean_object* v_map_750_; lean_object* v___x_751_; 
v_name_748_ = lean_ctor_get(v_opt_747_, 0);
v_defValue_749_ = lean_ctor_get(v_opt_747_, 1);
v_map_750_ = lean_ctor_get(v_opts_746_, 0);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_750_, v_name_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
uint8_t v___x_752_; 
v___x_752_ = lean_unbox(v_defValue_749_);
return v___x_752_;
}
else
{
lean_object* v_val_753_; 
v_val_753_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v___x_751_, 1);
if (lean_obj_tag(v_val_753_) == 1)
{
uint8_t v_v_754_; 
v_v_754_ = lean_ctor_get_uint8(v_val_753_, 0);
lean_dec_ref_known(v_val_753_, 0);
return v_v_754_;
}
else
{
uint8_t v___x_755_; 
lean_dec(v_val_753_);
v___x_755_ = lean_unbox(v_defValue_749_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_746_ = stack[0].m_obj;
lean_object* v_opt_747_ = stack[1].m_obj;
uint8_t v_res_756_;
v_res_756_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_746_, v_opt_747_);
stack->m_num = v_res_756_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_757_, lean_object* v_opt_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_757_, v_opt_758_);
lean_dec_ref(v_opt_758_);
lean_dec_ref(v_opts_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_env_768_; uint8_t v___x_769_; lean_object* v_env_770_; lean_object* v___x_771_; lean_object* v_toCold_772_; lean_object* v_mctx_773_; lean_object* v_lctx_774_; lean_object* v_options_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_767_ = lean_st_ref_get(v___y_765_);
v_env_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_ref(v_env_768_);
lean_dec(v___x_767_);
v___x_769_ = 0;
v_env_770_ = l_Lean_Environment_setRecordingDeps(v_env_768_, v___x_769_);
v___x_771_ = lean_st_ref_get(v___y_763_);
v_toCold_772_ = lean_ctor_get(v___y_764_, 0);
v_mctx_773_ = lean_ctor_get(v___x_771_, 0);
lean_inc_ref(v_mctx_773_);
lean_dec(v___x_771_);
v_lctx_774_ = lean_ctor_get(v___y_762_, 2);
v_options_775_ = lean_ctor_get(v_toCold_772_, 2);
lean_inc_ref(v_options_775_);
lean_inc_ref(v_lctx_774_);
v___x_776_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_776_, 0, v_env_770_);
lean_ctor_set(v___x_776_, 1, v_mctx_773_);
lean_ctor_set(v___x_776_, 2, v_lctx_774_);
lean_ctor_set(v___x_776_, 3, v_options_775_);
v___x_777_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_msgData_761_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_761_ = stack[0].m_obj;
lean_object* v___y_762_ = stack[1].m_obj;
lean_object* v___y_763_ = stack[2].m_obj;
lean_object* v___y_764_ = stack[3].m_obj;
lean_object* v___y_765_ = stack[4].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_787_, uint8_t v___y_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_789_) == 1)
{
lean_object* v_pre_790_; 
v_pre_790_ = lean_ctor_get(v_x_789_, 0);
switch(lean_obj_tag(v_pre_790_))
{
case 1:
{
lean_object* v_pre_791_; 
v_pre_791_ = lean_ctor_get(v_pre_790_, 0);
switch(lean_obj_tag(v_pre_791_))
{
case 0:
{
lean_object* v_str_792_; lean_object* v_str_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_str_792_ = lean_ctor_get(v_x_789_, 1);
v_str_793_ = lean_ctor_get(v_pre_790_, 1);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_795_ = lean_string_dec_eq(v_str_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_797_ = lean_string_dec_eq(v_str_793_, v___x_796_);
if (v___x_797_ == 0)
{
return v___x_797_;
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_799_ = lean_string_dec_eq(v_str_792_, v___x_798_);
if (v___x_799_ == 0)
{
return v___x_799_;
}
else
{
return v_suppressElabErrors_787_;
}
}
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_801_ = lean_string_dec_eq(v_str_792_, v___x_800_);
if (v___x_801_ == 0)
{
return v___x_801_;
}
else
{
return v_suppressElabErrors_787_;
}
}
}
case 1:
{
lean_object* v_pre_802_; 
v_pre_802_ = lean_ctor_get(v_pre_791_, 0);
if (lean_obj_tag(v_pre_802_) == 0)
{
lean_object* v_str_803_; lean_object* v_str_804_; lean_object* v_str_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_str_803_ = lean_ctor_get(v_x_789_, 1);
v_str_804_ = lean_ctor_get(v_pre_790_, 1);
v_str_805_ = lean_ctor_get(v_pre_791_, 1);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_807_ = lean_string_dec_eq(v_str_805_, v___x_806_);
if (v___x_807_ == 0)
{
return v___x_807_;
}
else
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_809_ = lean_string_dec_eq(v_str_804_, v___x_808_);
if (v___x_809_ == 0)
{
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_811_ = lean_string_dec_eq(v_str_803_, v___x_810_);
if (v___x_811_ == 0)
{
return v___x_811_;
}
else
{
return v_suppressElabErrors_787_;
}
}
}
}
else
{
return v___y_788_;
}
}
default: 
{
return v___y_788_;
}
}
}
case 0:
{
lean_object* v_str_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_str_812_ = lean_ctor_get(v_x_789_, 1);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_814_ = lean_string_dec_eq(v_str_812_, v___x_813_);
if (v___x_814_ == 0)
{
return v___x_814_;
}
else
{
return v_suppressElabErrors_787_;
}
}
default: 
{
return v___y_788_;
}
}
}
else
{
return v___y_788_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_787_ = stack[0].m_num;
uint8_t v___y_788_ = stack[1].m_num;
lean_object* v_x_789_ = stack[2].m_obj;
uint8_t v_res_815_;
v_res_815_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_787_, v___y_788_, v_x_789_);
stack->m_num = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_816_, lean_object* v___y_817_, lean_object* v_x_818_){
_start:
{
uint8_t v_suppressElabErrors_boxed_819_; uint8_t v___y_9979__boxed_820_; uint8_t v_res_821_; lean_object* v_r_822_; 
v_suppressElabErrors_boxed_819_ = lean_unbox(v_suppressElabErrors_816_);
v___y_9979__boxed_820_ = lean_unbox(v___y_817_);
v_res_821_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_819_, v___y_9979__boxed_820_, v_x_818_);
lean_dec(v_x_818_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_823_, lean_object* v_msgData_824_, uint8_t v_severity_825_, uint8_t v_isSilent_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; lean_object* v_toCold_840_; lean_object* v___y_841_; lean_object* v___y_870_; lean_object* v___y_871_; uint8_t v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; uint8_t v___y_875_; uint8_t v___y_876_; lean_object* v___y_877_; lean_object* v___y_897_; lean_object* v___y_898_; uint8_t v___y_899_; lean_object* v___y_900_; uint8_t v___y_901_; uint8_t v___y_902_; lean_object* v___y_903_; uint8_t v___y_907_; uint8_t v___y_908_; uint8_t v___y_909_; uint8_t v___x_920_; uint8_t v___y_922_; uint8_t v___y_923_; uint8_t v___y_924_; uint8_t v___y_926_; uint8_t v___x_934_; 
v___x_920_ = 2;
v___x_934_ = l_Lean_instBEqMessageSeverity_beq(v_severity_825_, v___x_920_);
if (v___x_934_ == 0)
{
v___y_926_ = v___x_934_;
goto v___jp_925_;
}
else
{
uint8_t v___x_935_; 
lean_inc_ref(v_msgData_824_);
v___x_935_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_824_);
v___y_926_ = v___x_935_;
goto v___jp_925_;
}
v___jp_832_:
{
lean_object* v_currNamespace_842_; lean_object* v_openDecls_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_env_848_; lean_object* v_nextMacroScope_849_; lean_object* v_ngen_850_; lean_object* v_auxDeclNGen_851_; lean_object* v_traceState_852_; lean_object* v_cache_853_; lean_object* v_recordedDeps_854_; lean_object* v_messages_855_; lean_object* v_infoState_856_; lean_object* v_snapshotTasks_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_868_; 
v_currNamespace_842_ = lean_ctor_get(v_toCold_840_, 4);
v_openDecls_843_ = lean_ctor_get(v_toCold_840_, 5);
lean_inc(v_openDecls_843_);
lean_inc(v_currNamespace_842_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_currNamespace_842_);
lean_ctor_set(v___x_844_, 1, v_openDecls_843_);
v___x_845_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___y_835_);
lean_inc_ref(v___y_837_);
lean_inc_ref(v___y_836_);
v___x_846_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_846_, 0, v___y_836_);
lean_ctor_set(v___x_846_, 1, v___y_838_);
lean_ctor_set(v___x_846_, 2, v___y_834_);
lean_ctor_set(v___x_846_, 3, v___y_837_);
lean_ctor_set(v___x_846_, 4, v___x_845_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*5, v___y_839_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*5 + 1, v___y_833_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*5 + 2, v_isSilent_826_);
v___x_847_ = lean_st_ref_take(v___y_841_);
v_env_848_ = lean_ctor_get(v___x_847_, 0);
v_nextMacroScope_849_ = lean_ctor_get(v___x_847_, 1);
v_ngen_850_ = lean_ctor_get(v___x_847_, 2);
v_auxDeclNGen_851_ = lean_ctor_get(v___x_847_, 3);
v_traceState_852_ = lean_ctor_get(v___x_847_, 4);
v_cache_853_ = lean_ctor_get(v___x_847_, 5);
v_recordedDeps_854_ = lean_ctor_get(v___x_847_, 6);
v_messages_855_ = lean_ctor_get(v___x_847_, 7);
v_infoState_856_ = lean_ctor_get(v___x_847_, 8);
v_snapshotTasks_857_ = lean_ctor_get(v___x_847_, 9);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_868_ == 0)
{
v___x_859_ = v___x_847_;
v_isShared_860_ = v_isSharedCheck_868_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snapshotTasks_857_);
lean_inc(v_infoState_856_);
lean_inc(v_messages_855_);
lean_inc(v_recordedDeps_854_);
lean_inc(v_cache_853_);
lean_inc(v_traceState_852_);
lean_inc(v_auxDeclNGen_851_);
lean_inc(v_ngen_850_);
lean_inc(v_nextMacroScope_849_);
lean_inc(v_env_848_);
lean_dec(v___x_847_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_868_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = lean_box(0);
v___x_862_ = l_Lean_MessageLog_add(v___x_846_, v_messages_855_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 7, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_env_848_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_nextMacroScope_849_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_ngen_850_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_auxDeclNGen_851_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_traceState_852_);
lean_ctor_set(v_reuseFailAlloc_867_, 5, v_cache_853_);
lean_ctor_set(v_reuseFailAlloc_867_, 6, v_recordedDeps_854_);
lean_ctor_set(v_reuseFailAlloc_867_, 7, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_867_, 8, v_infoState_856_);
lean_ctor_set(v_reuseFailAlloc_867_, 9, v_snapshotTasks_857_);
v___x_864_ = v_reuseFailAlloc_867_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_st_ref_put(v___y_841_, v___x_864_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_861_);
return v___x_866_;
}
}
}
v___jp_869_:
{
lean_object* v_fileName_878_; lean_object* v_fileMap_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_895_; 
v_fileName_878_ = lean_ctor_get(v___y_874_, 0);
v_fileMap_879_ = lean_ctor_get(v___y_874_, 1);
v___x_880_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_824_);
v___x_881_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_880_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_895_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_895_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_895_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_inc_ref_n(v_fileMap_879_, 2);
v___x_886_ = l_Lean_FileMap_toPosition(v_fileMap_879_, v___y_873_);
lean_dec(v___y_873_);
v___x_887_ = l_Lean_FileMap_toPosition(v_fileMap_879_, v___y_877_);
lean_dec(v___y_877_);
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
v___x_889_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_876_ == 0)
{
lean_del_object(v___x_884_);
lean_dec_ref(v___y_870_);
v___y_833_ = v___y_872_;
v___y_834_ = v___x_888_;
v___y_835_ = v_a_882_;
v___y_836_ = v_fileName_878_;
v___y_837_ = v___x_889_;
v___y_838_ = v___x_886_;
v___y_839_ = v___y_875_;
v_toCold_840_ = v___y_871_;
v___y_841_ = v___y_830_;
goto v___jp_832_;
}
else
{
uint8_t v___x_890_; 
lean_inc(v_a_882_);
v___x_890_ = l_Lean_MessageData_hasTag(v___y_870_, v_a_882_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_893_; 
lean_dec_ref_known(v___x_888_, 1);
lean_dec_ref(v___x_886_);
lean_dec(v_a_882_);
v___x_891_ = lean_box(0);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_891_);
v___x_893_ = v___x_884_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_del_object(v___x_884_);
v___y_833_ = v___y_872_;
v___y_834_ = v___x_888_;
v___y_835_ = v_a_882_;
v___y_836_ = v_fileName_878_;
v___y_837_ = v___x_889_;
v___y_838_ = v___x_886_;
v___y_839_ = v___y_875_;
v_toCold_840_ = v___y_871_;
v___y_841_ = v___y_830_;
goto v___jp_832_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Syntax_getTailPos_x3f(v___y_900_, v___y_902_);
lean_dec(v___y_900_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_inc(v___y_903_);
v___y_870_ = v___y_897_;
v___y_871_ = v___y_898_;
v___y_872_ = v___y_901_;
v___y_873_ = v___y_903_;
v___y_874_ = v___y_898_;
v___y_875_ = v___y_902_;
v___y_876_ = v___y_899_;
v___y_877_ = v___y_903_;
goto v___jp_869_;
}
else
{
lean_object* v_val_905_; 
v_val_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v___x_904_, 1);
v___y_870_ = v___y_897_;
v___y_871_ = v___y_898_;
v___y_872_ = v___y_901_;
v___y_873_ = v___y_903_;
v___y_874_ = v___y_898_;
v___y_875_ = v___y_902_;
v___y_876_ = v___y_899_;
v___y_877_ = v_val_905_;
goto v___jp_869_;
}
}
v___jp_906_:
{
lean_object* v_toCold_910_; lean_object* v_ref_911_; uint8_t v_suppressElabErrors_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v_ref_916_; lean_object* v___x_917_; 
v_toCold_910_ = lean_ctor_get(v___y_829_, 0);
v_ref_911_ = lean_ctor_get(v___y_829_, 2);
v_suppressElabErrors_912_ = lean_ctor_get_uint8(v___y_829_, sizeof(void*)*3 + 2);
v___x_913_ = lean_box(v_suppressElabErrors_912_);
v___x_914_ = lean_box(v___y_907_);
v___f_915_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_915_, 0, v___x_913_);
lean_closure_set(v___f_915_, 1, v___x_914_);
v_ref_916_ = l_Lean_replaceRef(v_ref_823_, v_ref_911_);
v___x_917_ = l_Lean_Syntax_getPos_x3f(v_ref_916_, v___y_908_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; 
v___x_918_ = lean_unsigned_to_nat(0u);
v___y_897_ = v___f_915_;
v___y_898_ = v_toCold_910_;
v___y_899_ = v_suppressElabErrors_912_;
v___y_900_ = v_ref_916_;
v___y_901_ = v___y_909_;
v___y_902_ = v___y_908_;
v___y_903_ = v___x_918_;
goto v___jp_896_;
}
else
{
lean_object* v_val_919_; 
v_val_919_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_val_919_);
lean_dec_ref_known(v___x_917_, 1);
v___y_897_ = v___f_915_;
v___y_898_ = v_toCold_910_;
v___y_899_ = v_suppressElabErrors_912_;
v___y_900_ = v_ref_916_;
v___y_901_ = v___y_909_;
v___y_902_ = v___y_908_;
v___y_903_ = v_val_919_;
goto v___jp_896_;
}
}
v___jp_921_:
{
if (v___y_924_ == 0)
{
v___y_907_ = v___y_922_;
v___y_908_ = v___y_923_;
v___y_909_ = v_severity_825_;
goto v___jp_906_;
}
else
{
v___y_907_ = v___y_922_;
v___y_908_ = v___y_923_;
v___y_909_ = v___x_920_;
goto v___jp_906_;
}
}
v___jp_925_:
{
if (v___y_926_ == 0)
{
uint8_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = 1;
v___x_928_ = l_Lean_instBEqMessageSeverity_beq(v_severity_825_, v___x_927_);
if (v___x_928_ == 0)
{
v___y_922_ = v___y_926_;
v___y_923_ = v___y_926_;
v___y_924_ = v___x_928_;
goto v___jp_921_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_829_);
v___x_930_ = l_Lean_warningAsError;
v___x_931_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_929_, v___x_930_);
lean_dec_ref(v___x_929_);
v___y_922_ = v___y_926_;
v___y_923_ = v___y_926_;
v___y_924_ = v___x_931_;
goto v___jp_921_;
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_msgData_824_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_823_ = stack[0].m_obj;
lean_object* v_msgData_824_ = stack[1].m_obj;
uint8_t v_severity_825_ = stack[2].m_num;
uint8_t v_isSilent_826_ = stack[3].m_num;
lean_object* v___y_827_ = stack[4].m_obj;
lean_object* v___y_828_ = stack[5].m_obj;
lean_object* v___y_829_ = stack[6].m_obj;
lean_object* v___y_830_ = stack[7].m_obj;
lean_object* v_res_936_;
v_res_936_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_823_, v_msgData_824_, v_severity_825_, v_isSilent_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_937_, lean_object* v_msgData_938_, lean_object* v_severity_939_, lean_object* v_isSilent_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v_severity_boxed_946_; uint8_t v_isSilent_boxed_947_; lean_object* v_res_948_; 
v_severity_boxed_946_ = lean_unbox(v_severity_939_);
v_isSilent_boxed_947_ = lean_unbox(v_isSilent_940_);
v_res_948_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_937_, v_msgData_938_, v_severity_boxed_946_, v_isSilent_boxed_947_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v_ref_937_);
return v_res_948_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_949_, size_t v_sz_950_, size_t v_i_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_b_952_);
return v___x_961_;
}
else
{
lean_object* v_ref_962_; lean_object* v_a_963_; uint8_t v_severity_964_; uint8_t v_isSilent_965_; lean_object* v_data_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_ref_962_ = lean_ctor_get(v___y_957_, 2);
v_a_963_ = lean_array_uget_borrowed(v_as_949_, v_i_951_);
v_severity_964_ = lean_ctor_get_uint8(v_a_963_, sizeof(void*)*5 + 1);
v_isSilent_965_ = lean_ctor_get_uint8(v_a_963_, sizeof(void*)*5 + 2);
v_data_966_ = lean_ctor_get(v_a_963_, 4);
v___x_967_ = lean_box(0);
lean_inc(v_data_966_);
v___x_968_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_962_, v_data_966_, v_severity_964_, v_isSilent_965_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_968_) == 0)
{
size_t v___x_969_; size_t v___x_970_; 
lean_dec_ref_known(v___x_968_, 1);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_951_, v___x_969_);
v_i_951_ = v___x_970_;
v_b_952_ = v___x_967_;
goto _start;
}
else
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_949_ = stack[0].m_obj;
size_t v_sz_950_ = stack[1].m_num;
size_t v_i_951_ = stack[2].m_num;
lean_object* v_b_952_ = stack[3].m_obj;
lean_object* v___y_953_ = stack[4].m_obj;
lean_object* v___y_954_ = stack[5].m_obj;
lean_object* v___y_955_ = stack[6].m_obj;
lean_object* v___y_956_ = stack[7].m_obj;
lean_object* v___y_957_ = stack[8].m_obj;
lean_object* v___y_958_ = stack[9].m_obj;
lean_object* v_res_972_;
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_949_, v_sz_950_, v_i_951_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_973_, lean_object* v_sz_974_, lean_object* v_i_975_, lean_object* v_b_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
size_t v_sz_boxed_984_; size_t v_i_boxed_985_; lean_object* v_res_986_; 
v_sz_boxed_984_ = lean_unbox_usize(v_sz_974_);
lean_dec(v_sz_974_);
v_i_boxed_985_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_973_, v_sz_boxed_984_, v_i_boxed_985_, v_b_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_as_973_);
return v_res_986_;
}
}
lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v_infoState_991_; lean_object* v_env_992_; lean_object* v_nextMacroScope_993_; lean_object* v_ngen_994_; lean_object* v_auxDeclNGen_995_; lean_object* v_traceState_996_; lean_object* v_cache_997_; lean_object* v_recordedDeps_998_; lean_object* v_messages_999_; lean_object* v_snapshotTasks_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1020_; 
v___x_990_ = lean_st_ref_take(v___y_988_);
v_infoState_991_ = lean_ctor_get(v___x_990_, 8);
v_env_992_ = lean_ctor_get(v___x_990_, 0);
v_nextMacroScope_993_ = lean_ctor_get(v___x_990_, 1);
v_ngen_994_ = lean_ctor_get(v___x_990_, 2);
v_auxDeclNGen_995_ = lean_ctor_get(v___x_990_, 3);
v_traceState_996_ = lean_ctor_get(v___x_990_, 4);
v_cache_997_ = lean_ctor_get(v___x_990_, 5);
v_recordedDeps_998_ = lean_ctor_get(v___x_990_, 6);
v_messages_999_ = lean_ctor_get(v___x_990_, 7);
v_snapshotTasks_1000_ = lean_ctor_get(v___x_990_, 9);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1002_ = v___x_990_;
v_isShared_1003_ = v_isSharedCheck_1020_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_snapshotTasks_1000_);
lean_inc(v_infoState_991_);
lean_inc(v_messages_999_);
lean_inc(v_recordedDeps_998_);
lean_inc(v_cache_997_);
lean_inc(v_traceState_996_);
lean_inc(v_auxDeclNGen_995_);
lean_inc(v_ngen_994_);
lean_inc(v_nextMacroScope_993_);
lean_inc(v_env_992_);
lean_dec(v___x_990_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1020_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_assignment_1004_; lean_object* v_lazyAssignment_1005_; lean_object* v_trees_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1019_; 
v_assignment_1004_ = lean_ctor_get(v_infoState_991_, 0);
v_lazyAssignment_1005_ = lean_ctor_get(v_infoState_991_, 1);
v_trees_1006_ = lean_ctor_get(v_infoState_991_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_infoState_991_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1008_ = v_infoState_991_;
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_trees_1006_);
lean_inc(v_lazyAssignment_1005_);
lean_inc(v_assignment_1004_);
lean_dec(v_infoState_991_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_assignment_1004_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_lazyAssignment_1005_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_trees_1006_);
v___x_1012_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*3, v_flag_987_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 8, v___x_1012_);
v___x_1014_ = v___x_1002_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_env_992_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_nextMacroScope_993_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_ngen_994_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_auxDeclNGen_995_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_traceState_996_);
lean_ctor_set(v_reuseFailAlloc_1017_, 5, v_cache_997_);
lean_ctor_set(v_reuseFailAlloc_1017_, 6, v_recordedDeps_998_);
lean_ctor_set(v_reuseFailAlloc_1017_, 7, v_messages_999_);
lean_ctor_set(v_reuseFailAlloc_1017_, 8, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1017_, 9, v_snapshotTasks_1000_);
v___x_1014_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_st_ref_put(v___y_988_, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1010_);
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_987_ = stack[0].m_num;
lean_object* v___y_988_ = stack[1].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_987_, v___y_988_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v_flag_boxed_1025_; lean_object* v_res_1026_; 
v_flag_boxed_1025_ = lean_unbox(v_flag_1022_);
v_res_1026_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1025_, v___y_1023_);
lean_dec(v___y_1023_);
return v_res_1026_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v_infoState_1037_; uint8_t v_enabled_1038_; lean_object* v_a_1040_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1036_ = lean_st_ref_get(v___y_1034_);
v_infoState_1037_ = lean_ctor_get(v___x_1036_, 8);
lean_inc_ref(v_infoState_1037_);
lean_dec(v___x_1036_);
v_enabled_1038_ = lean_ctor_get_uint8(v_infoState_1037_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1037_);
v___x_1050_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1027_, v___y_1034_);
lean_dec_ref(v___x_1050_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
v___x_1051_ = lean_apply_7(v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, lean_box(0));
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1038_, v___y_1034_);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___x_1053_, 0);
lean_dec(v_unused_1061_);
v___x_1055_ = v___x_1053_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_dec(v___x_1053_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1052_);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1052_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1062_; 
v_a_1062_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1051_, 1);
v_a_1040_ = v_a_1062_;
goto v___jp_1039_;
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v___x_1041_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1038_, v___y_1034_);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1041_, 0);
lean_dec(v_unused_1049_);
v___x_1043_ = v___x_1041_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v___x_1041_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
lean_ctor_set(v___x_1043_, 0, v_a_1040_);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1040_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_1027_ = stack[0].m_num;
lean_object* v_x_1028_ = stack[1].m_obj;
lean_object* v___y_1029_ = stack[2].m_obj;
lean_object* v___y_1030_ = stack[3].m_obj;
lean_object* v___y_1031_ = stack[4].m_obj;
lean_object* v___y_1032_ = stack[5].m_obj;
lean_object* v___y_1033_ = stack[6].m_obj;
lean_object* v___y_1034_ = stack[7].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1064_, lean_object* v_x_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v_flag_boxed_1073_; lean_object* v_res_1074_; 
v_flag_boxed_1073_ = lean_unbox(v_flag_1064_);
v_res_1074_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1073_, v_x_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1074_;
}
}
lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1075_, lean_object* v_binders_1076_, lean_object* v_blocks_1077_, lean_object* v_fileMap_x3f_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1084_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v_a_1089_; size_t v_sz_1107_; size_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___y_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v_sz_1107_ = lean_array_size(v_blocks_1077_);
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1107_, v___x_1108_, v_blocks_1077_);
v___x_1110_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1110_, 0, v___x_1109_);
v___x_1111_ = 1;
v___x_1112_ = lean_box(v___x_1111_);
v___y_1113_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1113_, 0, v_fileMap_x3f_1078_);
lean_closure_set(v___y_1113_, 1, v_declName_1075_);
lean_closure_set(v___y_1113_, 2, v_binders_1076_);
lean_closure_set(v___y_1113_, 3, v___x_1110_);
lean_closure_set(v___y_1113_, 4, v___x_1112_);
v___x_1114_ = 0;
v___x_1115_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1114_, v___y_1113_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1084_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_Core_setMessageLog___redArg(v_a_1087_, v_a_1084_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; size_t v_sz_1122_; lean_object* v___x_1123_; 
lean_dec_ref_known(v___x_1119_, 1);
v___x_1120_ = l_Lean_MessageLog_toArray(v_a_1118_);
lean_dec(v_a_1118_);
v___x_1121_ = lean_box(0);
v_sz_1122_ = lean_array_size(v___x_1120_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1120_, v_sz_1122_, v___x_1108_, v___x_1121_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec_ref(v___x_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1148_; 
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1149_);
v___x_1125_ = v___x_1123_;
v_isShared_1126_ = v_isSharedCheck_1148_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v___x_1123_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1148_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1147_; 
v_fst_1127_ = lean_ctor_get(v_a_1116_, 0);
v_snd_1128_ = lean_ctor_get(v_a_1116_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1116_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1130_ = v_a_1116_;
v_isShared_1131_ = v_isSharedCheck_1147_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_inc(v_fst_1127_);
lean_dec(v_a_1116_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1147_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_fst_1132_; lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1146_; 
v_fst_1132_ = lean_ctor_get(v_fst_1127_, 0);
v_snd_1133_ = lean_ctor_get(v_fst_1127_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_fst_1127_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1135_ = v_fst_1127_;
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_inc(v_fst_1132_);
lean_dec(v_fst_1127_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1146_;
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
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_fst_1132_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_snd_1133_);
v___x_1138_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1138_);
v___x_1140_ = v___x_1130_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_snd_1128_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1140_);
v___x_1142_ = v___x_1125_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
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
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1116_);
v_a_1150_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1123_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1123_);
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
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1118_);
lean_dec(v_a_1116_);
v_a_1158_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1119_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1119_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1166_; 
lean_dec(v_a_1116_);
v_a_1166_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1117_, 1);
v_a_1089_ = v_a_1166_;
goto v___jp_1088_;
}
}
else
{
lean_object* v_a_1167_; 
v_a_1167_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1115_, 1);
v_a_1089_ = v_a_1167_;
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Core_setMessageLog___redArg(v_a_1087_, v_a_1084_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1090_, 0);
lean_dec(v_unused_1098_);
v___x_1092_ = v___x_1090_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v___x_1090_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
lean_ctor_set(v___x_1092_, 0, v_a_1089_);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1089_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_a_1089_);
v_a_1099_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1090_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1090_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_fileMap_x3f_1078_);
lean_dec_ref(v_blocks_1077_);
lean_dec(v_binders_1076_);
lean_dec(v_declName_1075_);
v_a_1168_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1086_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1086_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Add_0__Lean_execVersoBlocks_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1075_ = stack[0].m_obj;
lean_object* v_binders_1076_ = stack[1].m_obj;
lean_object* v_blocks_1077_ = stack[2].m_obj;
lean_object* v_fileMap_x3f_1078_ = stack[3].m_obj;
lean_object* v_a_1079_ = stack[4].m_obj;
lean_object* v_a_1080_ = stack[5].m_obj;
lean_object* v_a_1081_ = stack[6].m_obj;
lean_object* v_a_1082_ = stack[7].m_obj;
lean_object* v_a_1083_ = stack[8].m_obj;
lean_object* v_a_1084_ = stack[9].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1075_, v_binders_1076_, v_blocks_1077_, v_fileMap_x3f_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1177_, lean_object* v_binders_1178_, lean_object* v_blocks_1179_, lean_object* v_fileMap_x3f_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1177_, v_binders_1178_, v_blocks_1179_, v_fileMap_x3f_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1188_;
}
}
lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1189_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_1189_ = stack[0].m_num;
lean_object* v___y_1190_ = stack[1].m_obj;
lean_object* v___y_1191_ = stack[2].m_obj;
lean_object* v___y_1192_ = stack[3].m_obj;
lean_object* v___y_1193_ = stack[4].m_obj;
lean_object* v___y_1194_ = stack[5].m_obj;
lean_object* v___y_1195_ = stack[6].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_flag_boxed_1207_; lean_object* v_res_1208_; 
v_flag_boxed_1207_ = lean_unbox(v_flag_1199_);
v_res_1208_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1207_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1208_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1209_, uint8_t v_flag_1210_, lean_object* v_x_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1210_, v_x_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_1210_ = stack[1].m_num;
lean_object* v_x_1211_ = stack[2].m_obj;
lean_object* v___y_1212_ = stack[3].m_obj;
lean_object* v___y_1213_ = stack[4].m_obj;
lean_object* v___y_1214_ = stack[5].m_obj;
lean_object* v___y_1215_ = stack[6].m_obj;
lean_object* v___y_1216_ = stack[7].m_obj;
lean_object* v___y_1217_ = stack[8].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_box(0), v_flag_1210_, v_x_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1221_, lean_object* v_flag_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_flag_boxed_1231_; lean_object* v_res_1232_; 
v_flag_boxed_1231_ = lean_unbox(v_flag_1222_);
v_res_1232_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1221_, v_flag_boxed_1231_, v_x_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1232_;
}
}
lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1233_, lean_object* v_msgData_1234_, uint8_t v_severity_1235_, uint8_t v_isSilent_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1233_, v_msgData_1234_, v_severity_1235_, v_isSilent_1236_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1233_ = stack[0].m_obj;
lean_object* v_msgData_1234_ = stack[1].m_obj;
uint8_t v_severity_1235_ = stack[2].m_num;
uint8_t v_isSilent_1236_ = stack[3].m_num;
lean_object* v___y_1237_ = stack[4].m_obj;
lean_object* v___y_1238_ = stack[5].m_obj;
lean_object* v___y_1239_ = stack[6].m_obj;
lean_object* v___y_1240_ = stack[7].m_obj;
lean_object* v___y_1241_ = stack[8].m_obj;
lean_object* v___y_1242_ = stack[9].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1233_, v_msgData_1234_, v_severity_1235_, v_isSilent_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1246_, lean_object* v_msgData_1247_, lean_object* v_severity_1248_, lean_object* v_isSilent_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_severity_boxed_1257_; uint8_t v_isSilent_boxed_1258_; lean_object* v_res_1259_; 
v_severity_boxed_1257_ = lean_unbox(v_severity_1248_);
v_isSilent_boxed_1258_ = lean_unbox(v_isSilent_1249_);
v_res_1259_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1246_, v_msgData_1247_, v_severity_boxed_1257_, v_isSilent_boxed_1258_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v_ref_1246_);
return v_res_1259_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1260_, uint8_t v_severity_1261_, uint8_t v_isSilent_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_ref_1268_; lean_object* v___x_1269_; 
v_ref_1268_ = lean_ctor_get(v___y_1265_, 2);
v___x_1269_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1268_, v_msgData_1260_, v_severity_1261_, v_isSilent_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1260_ = stack[0].m_obj;
uint8_t v_severity_1261_ = stack[1].m_num;
uint8_t v_isSilent_1262_ = stack[2].m_num;
lean_object* v___y_1263_ = stack[3].m_obj;
lean_object* v___y_1264_ = stack[4].m_obj;
lean_object* v___y_1265_ = stack[5].m_obj;
lean_object* v___y_1266_ = stack[6].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1260_, v_severity_1261_, v_isSilent_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1271_, lean_object* v_severity_1272_, lean_object* v_isSilent_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_severity_boxed_1279_; uint8_t v_isSilent_boxed_1280_; lean_object* v_res_1281_; 
v_severity_boxed_1279_ = lean_unbox(v_severity_1272_);
v_isSilent_boxed_1280_ = lean_unbox(v_isSilent_1273_);
v_res_1281_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1271_, v_severity_boxed_1279_, v_isSilent_boxed_1280_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1281_;
}
}
lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = 2;
v___x_1291_ = 0;
v___x_1292_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1282_, v___x_1290_, v___x_1291_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1292_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1282_ = stack[0].m_obj;
lean_object* v___y_1283_ = stack[1].m_obj;
lean_object* v___y_1284_ = stack[2].m_obj;
lean_object* v___y_1285_ = stack[3].m_obj;
lean_object* v___y_1286_ = stack[4].m_obj;
lean_object* v___y_1287_ = stack[5].m_obj;
lean_object* v___y_1288_ = stack[6].m_obj;
lean_object* v_res_1293_;
v_res_1293_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
stack->m_obj
 = v_res_1293_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1302_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1303_, size_t v_sz_1304_, size_t v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_lt(v_i_1305_, v_sz_1304_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_b_1306_);
return v___x_1315_;
}
else
{
lean_object* v_a_1316_; lean_object* v_snd_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_a_1316_ = lean_array_uget_borrowed(v_as_1303_, v_i_1305_);
v_snd_1317_ = lean_ctor_get(v_a_1316_, 1);
v_snd_1318_ = lean_ctor_get(v_snd_1317_, 1);
v___x_1319_ = lean_box(0);
lean_inc(v_snd_1318_);
v___x_1320_ = l_Lean_Parser_Error_toString(v_snd_1318_);
v___x_1321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___x_1322_ = l_Lean_MessageData_ofFormat(v___x_1321_);
v___x_1323_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1322_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1323_) == 0)
{
size_t v___x_1324_; size_t v___x_1325_; 
lean_dec_ref_known(v___x_1323_, 1);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_add(v_i_1305_, v___x_1324_);
v_i_1305_ = v___x_1325_;
v_b_1306_ = v___x_1319_;
goto _start;
}
else
{
return v___x_1323_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1303_ = stack[0].m_obj;
size_t v_sz_1304_ = stack[1].m_num;
size_t v_i_1305_ = stack[2].m_num;
lean_object* v_b_1306_ = stack[3].m_obj;
lean_object* v___y_1307_ = stack[4].m_obj;
lean_object* v___y_1308_ = stack[5].m_obj;
lean_object* v___y_1309_ = stack[6].m_obj;
lean_object* v___y_1310_ = stack[7].m_obj;
lean_object* v___y_1311_ = stack[8].m_obj;
lean_object* v___y_1312_ = stack[9].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1303_, v_sz_1304_, v_i_1305_, v_b_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1328_, lean_object* v_sz_1329_, lean_object* v_i_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1329_);
lean_dec(v_sz_1329_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1328_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec_ref(v_as_1328_);
return v_res_1341_;
}
}
lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1360_, lean_object* v_binders_1361_, lean_object* v_docComment_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_toCold_1371_; lean_object* v_env_1372_; lean_object* v_fileName_1373_; lean_object* v_currNamespace_1374_; lean_object* v_openDecls_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1370_ = lean_st_ref_get(v_a_1368_);
v_toCold_1371_ = lean_ctor_get(v_a_1367_, 0);
v_env_1372_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref_n(v_env_1372_, 2);
lean_dec(v___x_1370_);
v_fileName_1373_ = lean_ctor_get(v_toCold_1371_, 0);
v_currNamespace_1374_ = lean_ctor_get(v_toCold_1371_, 4);
v_openDecls_1375_ = lean_ctor_get(v_toCold_1371_, 5);
v___x_1376_ = lean_string_utf8_byte_size(v_docComment_1362_);
lean_inc_ref_n(v_docComment_1362_, 2);
v___x_1377_ = l_Lean_FileMap_ofString(v_docComment_1362_);
lean_inc_ref(v___x_1377_);
lean_inc_ref(v_fileName_1373_);
v___x_1378_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1378_, 0, v_docComment_1362_);
lean_ctor_set(v___x_1378_, 1, v_fileName_1373_);
lean_ctor_set(v___x_1378_, 2, v___x_1377_);
lean_ctor_set(v___x_1378_, 3, v___x_1376_);
v___x_1379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1367_);
lean_inc(v_openDecls_1375_);
lean_inc(v_currNamespace_1374_);
v___x_1380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1380_, 0, v_env_1372_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_ctor_set(v___x_1380_, 2, v_currNamespace_1374_);
lean_ctor_set(v___x_1380_, 3, v_openDecls_1375_);
v___x_1381_ = l_Lean_Parser_mkParserState(v_docComment_1362_);
lean_dec_ref(v_docComment_1362_);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1384_ = l_Lean_Parser_getTokenTable(v_env_1372_);
v___x_1385_ = l_Lean_Parser_ParserFn_run(v___x_1383_, v___x_1378_, v___x_1380_, v___x_1384_, v___x_1381_);
lean_inc_ref(v___x_1385_);
v___x_1386_ = l_Lean_Parser_ParserState_allErrors(v___x_1385_);
v___x_1387_ = lean_array_get_size(v___x_1386_);
v___x_1388_ = lean_nat_dec_eq(v___x_1387_, v___x_1382_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; size_t v_sz_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v___x_1385_);
lean_dec_ref(v___x_1377_);
lean_dec(v_binders_1361_);
lean_dec(v_declName_1360_);
v___x_1389_ = lean_box(0);
v_sz_1390_ = lean_array_size(v___x_1386_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1386_, v_sz_1390_, v___x_1391_, v___x_1389_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec_ref(v___x_1386_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1392_, 0);
lean_dec(v_unused_1401_);
v___x_1394_ = v___x_1392_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v___x_1392_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1392_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1392_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v_stxStack_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref(v___x_1386_);
v_stxStack_1410_ = lean_ctor_get(v___x_1385_, 0);
lean_inc_ref(v_stxStack_1410_);
lean_dec_ref(v___x_1385_);
v___x_1411_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1410_);
lean_dec_ref(v_stxStack_1410_);
v___x_1412_ = l_Lean_TSyntax_getVersoBlocks(v___x_1411_);
lean_dec(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1377_);
v___x_1414_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1360_, v_binders_1361_, v___x_1412_, v___x_1413_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1414_;
}
}
}
LEAN_EXPORT void l_Lean_versoDocStringOfText_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1360_ = stack[0].m_obj;
lean_object* v_binders_1361_ = stack[1].m_obj;
lean_object* v_docComment_1362_ = stack[2].m_obj;
lean_object* v_a_1363_ = stack[3].m_obj;
lean_object* v_a_1364_ = stack[4].m_obj;
lean_object* v_a_1365_ = stack[5].m_obj;
lean_object* v_a_1366_ = stack[6].m_obj;
lean_object* v_a_1367_ = stack[7].m_obj;
lean_object* v_a_1368_ = stack[8].m_obj;
lean_object* v_res_1415_;
v_res_1415_ = l_Lean_versoDocStringOfText(v_declName_1360_, v_binders_1361_, v_docComment_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
stack->m_obj
 = v_res_1415_;
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1416_, lean_object* v_binders_1417_, lean_object* v_docComment_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_versoDocStringOfText(v_declName_1416_, v_binders_1417_, v_docComment_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
return v_res_1426_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1427_, uint8_t v_severity_1428_, uint8_t v_isSilent_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1427_, v_severity_1428_, v_isSilent_1429_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1427_ = stack[0].m_obj;
uint8_t v_severity_1428_ = stack[1].m_num;
uint8_t v_isSilent_1429_ = stack[2].m_num;
lean_object* v___y_1430_ = stack[3].m_obj;
lean_object* v___y_1431_ = stack[4].m_obj;
lean_object* v___y_1432_ = stack[5].m_obj;
lean_object* v___y_1433_ = stack[6].m_obj;
lean_object* v___y_1434_ = stack[7].m_obj;
lean_object* v___y_1435_ = stack[8].m_obj;
lean_object* v_res_1438_;
v_res_1438_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1427_, v_severity_1428_, v_isSilent_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
stack->m_obj
 = v_res_1438_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1439_, lean_object* v_severity_1440_, lean_object* v_isSilent_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_severity_boxed_1449_; uint8_t v_isSilent_boxed_1450_; lean_object* v_res_1451_; 
v_severity_boxed_1449_ = lean_unbox(v_severity_1440_);
v_isSilent_boxed_1450_ = lean_unbox(v_isSilent_1441_);
v_res_1451_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1439_, v_severity_boxed_1449_, v_isSilent_boxed_1450_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1451_;
}
}
lean_object* l_Lean_versoDocString(lean_object* v_declName_1461_, lean_object* v_binders_1462_, lean_object* v_docComment_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1463_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; lean_object* v_body_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
lean_dec_ref_known(v___x_1471_, 1);
v___x_1472_ = lean_unsigned_to_nat(1u);
v_body_1473_ = l_Lean_Syntax_getArg(v_docComment_1463_, v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_1475_ = l_Lean_Syntax_isOfKind(v_body_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = l_Lean_TSyntax_getDocString(v_docComment_1463_);
v___x_1477_ = l_Lean_versoDocStringOfText(v_declName_1461_, v_binders_1462_, v___x_1476_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; lean_object* v_markup_1479_; 
v___x_1478_ = l_Lean_VersoDocstringView_of(v_docComment_1463_);
v_markup_1479_ = lean_ctor_get(v___x_1478_, 1);
lean_inc_ref(v_markup_1479_);
lean_dec_ref(v___x_1478_);
if (lean_obj_tag(v_markup_1479_) == 0)
{
lean_object* v_doc_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_doc_1480_ = lean_ctor_get(v_markup_1479_, 0);
lean_inc(v_doc_1480_);
lean_dec_ref_known(v_markup_1479_, 1);
v___x_1481_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1480_);
lean_dec(v_doc_1480_);
v___x_1482_ = lean_box(0);
v___x_1483_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1461_, v_binders_1462_, v___x_1481_, v___x_1482_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1483_;
}
else
{
lean_object* v_text_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_text_1484_ = lean_ctor_get(v_markup_1479_, 0);
lean_inc(v_text_1484_);
lean_dec_ref_known(v_markup_1479_, 1);
v___x_1485_ = l_Lean_Syntax_getAtomVal(v_text_1484_);
lean_dec(v_text_1484_);
v___x_1486_ = l_Lean_versoDocStringOfText(v_declName_1461_, v_binders_1462_, v___x_1485_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1486_;
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec_ref_known(v___x_1471_, 1);
v___x_1487_ = l_Lean_parseVersoDocString(v_docComment_1463_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1535_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1535_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1535_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
if (lean_obj_tag(v_a_1488_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; 
lean_del_object(v___x_1490_);
v_val_1492_ = lean_ctor_get(v_a_1488_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_a_1488_, 1);
v___x_1493_ = l_Lean_TSyntax_getVersoBlocks(v_val_1492_);
lean_dec(v_val_1492_);
v___x_1494_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = 0;
v___x_1496_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1461_, v_binders_1462_, v___x_1494_, v___x_1495_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1522_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1522_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1522_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1521_; 
v_fst_1501_ = lean_ctor_get(v_a_1497_, 0);
v_snd_1502_ = lean_ctor_get(v_a_1497_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_a_1497_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1504_ = v_a_1497_;
v_isShared_1505_ = v_isSharedCheck_1521_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_snd_1502_);
lean_inc(v_fst_1501_);
lean_dec(v_a_1497_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1521_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_fst_1506_; lean_object* v_snd_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1520_; 
v_fst_1506_ = lean_ctor_get(v_fst_1501_, 0);
v_snd_1507_ = lean_ctor_get(v_fst_1501_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_fst_1501_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1509_ = v_fst_1501_;
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snd_1507_);
lean_inc(v_fst_1506_);
lean_dec(v_fst_1501_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1520_;
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
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_fst_1506_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_snd_1507_);
v___x_1512_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1512_);
v___x_1514_ = v___x_1504_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_snd_1502_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1514_);
v___x_1516_ = v___x_1499_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_a_1523_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1496_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1496_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v_a_1488_);
lean_dec(v_binders_1462_);
lean_dec(v_declName_1461_);
v___x_1531_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1531_);
v___x_1533_ = v___x_1490_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_binders_1462_);
lean_dec(v_declName_1461_);
v_a_1536_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1487_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1487_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_versoDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1461_ = stack[0].m_obj;
lean_object* v_binders_1462_ = stack[1].m_obj;
lean_object* v_docComment_1463_ = stack[2].m_obj;
lean_object* v_a_1464_ = stack[3].m_obj;
lean_object* v_a_1465_ = stack[4].m_obj;
lean_object* v_a_1466_ = stack[5].m_obj;
lean_object* v_a_1467_ = stack[6].m_obj;
lean_object* v_a_1468_ = stack[7].m_obj;
lean_object* v_a_1469_ = stack[8].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l_Lean_versoDocString(v_declName_1461_, v_binders_1462_, v_docComment_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1545_, lean_object* v_binders_1546_, lean_object* v_docComment_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_versoDocString(v_declName_1545_, v_binders_1546_, v_docComment_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_docComment_1547_);
return v_res_1555_;
}
}
lean_object* l_Lean_versoModDocString(lean_object* v_range_1556_, lean_object* v_doc_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v_val_1573_; lean_object* v_env_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1565_ = lean_st_ref_get(v_a_1563_);
v_env_1575_ = lean_ctor_get(v___x_1565_, 0);
lean_inc_ref(v_env_1575_);
lean_dec(v___x_1565_);
v___x_1576_ = l_Lean_getMainVersoModuleDocs(v_env_1575_);
v___x_1577_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1576_);
lean_dec_ref(v___x_1576_);
if (lean_obj_tag(v___x_1577_) == 0)
{
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1557_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___y_1567_ = v___x_1578_;
v___y_1568_ = v___x_1579_;
goto v___jp_1566_;
}
else
{
lean_object* v_val_1580_; 
v_val_1580_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1577_, 1);
v_val_1573_ = v_val_1580_;
goto v___jp_1572_;
}
}
else
{
lean_object* v_val_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_val_1581_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_nat_add(v_val_1581_, v___x_1582_);
lean_dec(v_val_1581_);
v_val_1573_ = v___x_1583_;
goto v___jp_1572_;
}
v___jp_1566_:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1569_, 0, v_range_1556_);
lean_closure_set(v___x_1569_, 1, v___y_1567_);
lean_closure_set(v___x_1569_, 2, v___y_1568_);
v___x_1570_ = 0;
v___x_1571_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1569_, v___x_1570_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
return v___x_1571_;
}
v___jp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1557_);
v___y_1567_ = v___x_1574_;
v___y_1568_ = v_val_1573_;
goto v___jp_1566_;
}
}
}
LEAN_EXPORT void l_Lean_versoModDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_1556_ = stack[0].m_obj;
lean_object* v_doc_1557_ = stack[1].m_obj;
lean_object* v_a_1558_ = stack[2].m_obj;
lean_object* v_a_1559_ = stack[3].m_obj;
lean_object* v_a_1560_ = stack[4].m_obj;
lean_object* v_a_1561_ = stack[5].m_obj;
lean_object* v_a_1562_ = stack[6].m_obj;
lean_object* v_a_1563_ = stack[7].m_obj;
lean_object* v_res_1584_;
v_res_1584_ = l_Lean_versoModDocString(v_range_1556_, v_doc_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
stack->m_obj
 = v_res_1584_;
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1585_, lean_object* v_doc_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_versoModDocString(v_range_1585_, v_doc_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_doc_1586_);
return v_res_1594_;
}
}
lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1604_, lean_object* v_docComment_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1614_ = l_Lean_versoDocStringOfText(v_declName_1604_, v___x_1613_, v_docComment_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Lean_versoDocStringFromString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1604_ = stack[0].m_obj;
lean_object* v_docComment_1605_ = stack[1].m_obj;
lean_object* v_a_1606_ = stack[2].m_obj;
lean_object* v_a_1607_ = stack[3].m_obj;
lean_object* v_a_1608_ = stack[4].m_obj;
lean_object* v_a_1609_ = stack[5].m_obj;
lean_object* v_a_1610_ = stack[6].m_obj;
lean_object* v_a_1611_ = stack[7].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l_Lean_versoDocStringFromString(v_declName_1604_, v_docComment_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1616_, lean_object* v_docComment_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_versoDocStringFromString(v_declName_1616_, v_docComment_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1625_;
}
}
lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1626_, lean_object* v_declName_1627_, uint8_t v___x_1628_, lean_object* v_env_1629_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = l_Lean_docStringExt;
v___x_1631_ = l_String_removeLeadingSpaces(v_docString_1626_);
v___x_1632_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1630_, v_env_1629_, v_declName_1627_, v___x_1631_, v___x_1628_);
return v___x_1632_;
}
}
LEAN_EXPORT void l_Lean_addMarkdownDocString___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_docString_1626_ = stack[0].m_obj;
lean_object* v_declName_1627_ = stack[1].m_obj;
uint8_t v___x_1628_ = stack[2].m_num;
lean_object* v_env_1629_ = stack[3].m_obj;
lean_object* v_res_1633_;
v_res_1633_ = l_Lean_addMarkdownDocString___redArg___lam__0(v_docString_1626_, v_declName_1627_, v___x_1628_, v_env_1629_);
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0___boxed(lean_object* v_docString_1634_, lean_object* v_declName_1635_, lean_object* v___x_1636_, lean_object* v_env_1637_){
_start:
{
uint8_t v___x_183__boxed_1638_; lean_object* v_res_1639_; 
v___x_183__boxed_1638_ = lean_unbox(v___x_1636_);
v_res_1639_ = l_Lean_addMarkdownDocString___redArg___lam__0(v_docString_1634_, v_declName_1635_, v___x_183__boxed_1638_, v_env_1637_);
return v_res_1639_;
}
}
lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1640_, uint8_t v___x_1641_, lean_object* v_modifyEnv_1642_, lean_object* v_docString_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(v___x_1641_);
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1645_, 0, v_docString_1643_);
lean_closure_set(v___f_1645_, 1, v_declName_1640_);
lean_closure_set(v___f_1645_, 2, v___x_1644_);
v___x_1646_ = lean_apply_1(v_modifyEnv_1642_, v___f_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT void l_Lean_addMarkdownDocString___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1640_ = stack[0].m_obj;
uint8_t v___x_1641_ = stack[1].m_num;
lean_object* v_modifyEnv_1642_ = stack[2].m_obj;
lean_object* v_docString_1643_ = stack[3].m_obj;
lean_object* v_res_1647_;
v_res_1647_ = l_Lean_addMarkdownDocString___redArg___lam__1(v_declName_1640_, v___x_1641_, v_modifyEnv_1642_, v_docString_1643_);
stack->m_obj
 = v_res_1647_;
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1___boxed(lean_object* v_declName_1648_, lean_object* v___x_1649_, lean_object* v_modifyEnv_1650_, lean_object* v_docString_1651_){
_start:
{
uint8_t v___x_197__boxed_1652_; lean_object* v_res_1653_; 
v___x_197__boxed_1652_ = lean_unbox(v___x_1649_);
v_res_1653_ = l_Lean_addMarkdownDocString___redArg___lam__1(v_declName_1648_, v___x_197__boxed_1652_, v_modifyEnv_1650_, v_docString_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_docComment_1656_, lean_object* v_toBind_1657_, lean_object* v___f_1658_, lean_object* v_____r_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = l_Lean_getDocStringText___redArg(v_inst_1654_, v_inst_1655_, v_docComment_1656_);
v___x_1661_ = lean_apply_4(v_toBind_1657_, lean_box(0), lean_box(0), v___x_1660_, v___f_1658_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_docComment_1667_, lean_object* v_toBind_1668_, lean_object* v___f_1669_, lean_object* v_____r_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = l_Lean_validateDocComment___redArg(v_inst_1662_, v_inst_1663_, v_inst_1664_, v_inst_1665_, v_inst_1666_, v_docComment_1667_);
v___x_1672_ = lean_apply_4(v_toBind_1668_, lean_box(0), lean_box(0), v___x_1671_, v___f_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_docComment_1678_, lean_object* v_toBind_1679_, lean_object* v___f_1680_, lean_object* v_____r_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_docComment_1678_, v_toBind_1679_, v___f_1680_, v_____r_1681_);
lean_dec(v_docComment_1678_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1683_, lean_object* v_____r_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_apply_1(v___f_1683_, v_____r_1684_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1688_ = l_Lean_stringToMessageData(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_1692_, lean_object* v_declName_1693_, uint8_t v___x_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_toBind_1697_, lean_object* v___f_1698_, lean_object* v_____do__lift_1699_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1699_, v_declName_1693_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_dec(v___f_1698_);
lean_dec(v_toBind_1697_);
lean_dec_ref(v_inst_1696_);
lean_dec_ref(v_inst_1695_);
lean_dec(v_declName_1693_);
goto v___jp_1700_;
}
else
{
lean_dec_ref_known(v___x_1703_, 1);
if (v___x_1694_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v___f_1692_);
v___x_1704_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1705_ = l_Lean_MessageData_ofConstName(v_declName_1693_, v___x_1694_);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_Lean_throwError___redArg(v_inst_1695_, v_inst_1696_, v___x_1708_);
v___x_1710_ = lean_apply_4(v_toBind_1697_, lean_box(0), lean_box(0), v___x_1709_, v___f_1698_);
return v___x_1710_;
}
else
{
lean_dec(v___f_1698_);
lean_dec(v_toBind_1697_);
lean_dec_ref(v_inst_1696_);
lean_dec_ref(v_inst_1695_);
lean_dec(v_declName_1693_);
goto v___jp_1700_;
}
}
v___jp_1700_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_apply_1(v___f_1692_, v___x_1701_);
return v___x_1702_;
}
}
}
LEAN_EXPORT void l_Lean_addMarkdownDocString___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1692_ = stack[0].m_obj;
lean_object* v_declName_1693_ = stack[1].m_obj;
uint8_t v___x_1694_ = stack[2].m_num;
lean_object* v_inst_1695_ = stack[3].m_obj;
lean_object* v_inst_1696_ = stack[4].m_obj;
lean_object* v_toBind_1697_ = stack[5].m_obj;
lean_object* v___f_1698_ = stack[6].m_obj;
lean_object* v_____do__lift_1699_ = stack[7].m_obj;
lean_object* v_res_1711_;
v_res_1711_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_1692_, v_declName_1693_, v___x_1694_, v_inst_1695_, v_inst_1696_, v_toBind_1697_, v___f_1698_, v_____do__lift_1699_);
stack->m_obj
 = v_res_1711_;
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_1712_, lean_object* v_declName_1713_, lean_object* v___x_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_toBind_1717_, lean_object* v___f_1718_, lean_object* v_____do__lift_1719_){
_start:
{
uint8_t v___x_292__boxed_1720_; lean_object* v_res_1721_; 
v___x_292__boxed_1720_ = lean_unbox(v___x_1714_);
v_res_1721_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_1712_, v_declName_1713_, v___x_292__boxed_1720_, v_inst_1715_, v_inst_1716_, v_toBind_1717_, v___f_1718_, v_____do__lift_1719_);
lean_dec_ref(v_____do__lift_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_declName_1729_, lean_object* v_docComment_1730_){
_start:
{
lean_object* v_toApplicative_1731_; lean_object* v_toBind_1732_; lean_object* v_toPure_1733_; uint8_t v___x_1734_; 
v_toApplicative_1731_ = lean_ctor_get(v_inst_1722_, 0);
v_toBind_1732_ = lean_ctor_get(v_inst_1722_, 1);
lean_inc(v_toBind_1732_);
v_toPure_1733_ = lean_ctor_get(v_toApplicative_1731_, 1);
v___x_1734_ = l_Lean_Name_isAnonymous(v_declName_1729_);
if (v___x_1734_ == 0)
{
lean_object* v_getEnv_1735_; lean_object* v_modifyEnv_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___f_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___x_1745_; 
v_getEnv_1735_ = lean_ctor_get(v_inst_1725_, 0);
lean_inc(v_getEnv_1735_);
v_modifyEnv_1736_ = lean_ctor_get(v_inst_1725_, 1);
lean_inc(v_modifyEnv_1736_);
lean_dec_ref(v_inst_1725_);
v___x_1737_ = 1;
v___x_1738_ = lean_box(v___x_1737_);
lean_inc(v_declName_1729_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1739_, 0, v_declName_1729_);
lean_closure_set(v___f_1739_, 1, v___x_1738_);
lean_closure_set(v___f_1739_, 2, v_modifyEnv_1736_);
lean_inc_n(v_toBind_1732_, 3);
lean_inc(v_docComment_1730_);
lean_inc_ref(v_inst_1726_);
lean_inc_ref_n(v_inst_1722_, 2);
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1740_, 0, v_inst_1722_);
lean_closure_set(v___f_1740_, 1, v_inst_1726_);
lean_closure_set(v___f_1740_, 2, v_docComment_1730_);
lean_closure_set(v___f_1740_, 3, v_toBind_1732_);
lean_closure_set(v___f_1740_, 4, v___f_1739_);
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1741_, 0, v_inst_1722_);
lean_closure_set(v___f_1741_, 1, v_inst_1723_);
lean_closure_set(v___f_1741_, 2, v_inst_1727_);
lean_closure_set(v___f_1741_, 3, v_inst_1728_);
lean_closure_set(v___f_1741_, 4, v_inst_1724_);
lean_closure_set(v___f_1741_, 5, v_docComment_1730_);
lean_closure_set(v___f_1741_, 6, v_toBind_1732_);
lean_closure_set(v___f_1741_, 7, v___f_1740_);
lean_inc_ref(v___f_1741_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1742_, 0, v___f_1741_);
v___x_1743_ = lean_box(v___x_1734_);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1744_, 0, v___f_1741_);
lean_closure_set(v___f_1744_, 1, v_declName_1729_);
lean_closure_set(v___f_1744_, 2, v___x_1743_);
lean_closure_set(v___f_1744_, 3, v_inst_1722_);
lean_closure_set(v___f_1744_, 4, v_inst_1726_);
lean_closure_set(v___f_1744_, 5, v_toBind_1732_);
lean_closure_set(v___f_1744_, 6, v___f_1742_);
v___x_1745_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v_getEnv_1735_, v___f_1744_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc(v_toPure_1733_);
lean_dec(v_toBind_1732_);
lean_dec(v_docComment_1730_);
lean_dec(v_declName_1729_);
lean_dec(v_inst_1728_);
lean_dec_ref(v_inst_1727_);
lean_dec_ref(v_inst_1726_);
lean_dec_ref(v_inst_1725_);
lean_dec_ref(v_inst_1724_);
lean_dec(v_inst_1723_);
lean_dec_ref(v_inst_1722_);
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_apply_2(v_toPure_1733_, lean_box(0), v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_declName_1756_, lean_object* v_docComment_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_addMarkdownDocString___redArg(v_inst_1749_, v_inst_1750_, v_inst_1751_, v_inst_1752_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v_declName_1756_, v_docComment_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v___x_1759_, lean_object* v___x_1760_, lean_object* v_s_1761_){
_start:
{
lean_object* v_addEntryFn_1762_; lean_object* v_importedEntries_1763_; lean_object* v_state_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
v_addEntryFn_1762_ = lean_ctor_get(v___x_1759_, 3);
lean_inc(v_addEntryFn_1762_);
lean_dec_ref(v___x_1759_);
v_importedEntries_1763_ = lean_ctor_get(v_s_1761_, 0);
v_state_1764_ = lean_ctor_get(v_s_1761_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_s_1761_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1766_ = v_s_1761_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_state_1764_);
lean_inc(v_importedEntries_1763_);
lean_dec(v_s_1761_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_state_1768_; lean_object* v___x_1770_; 
v_state_1768_ = lean_apply_2(v_addEntryFn_1762_, v_state_1764_, v___x_1760_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v_state_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_importedEntries_1763_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_state_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1773_, lean_object* v_x1_1774_, lean_object* v_x2_1775_){
_start:
{
lean_object* v_index_1776_; lean_object* v_sourceString_1777_; lean_object* v_imports_1778_; lean_object* v_currNamespace_1779_; lean_object* v_openDecls_1780_; lean_object* v_options_1781_; lean_object* v_check_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1800_; 
v_index_1776_ = lean_ctor_get(v_x2_1775_, 1);
v_sourceString_1777_ = lean_ctor_get(v_x2_1775_, 2);
v_imports_1778_ = lean_ctor_get(v_x2_1775_, 3);
v_currNamespace_1779_ = lean_ctor_get(v_x2_1775_, 4);
v_openDecls_1780_ = lean_ctor_get(v_x2_1775_, 5);
v_options_1781_ = lean_ctor_get(v_x2_1775_, 6);
v_check_1782_ = lean_ctor_get(v_x2_1775_, 7);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_x2_1775_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_x2_1775_, 0);
lean_dec(v_unused_1801_);
v___x_1784_ = v_x2_1775_;
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_check_1782_);
lean_inc(v_options_1781_);
lean_inc(v_openDecls_1780_);
lean_inc(v_currNamespace_1779_);
lean_inc(v_imports_1778_);
lean_inc(v_sourceString_1777_);
lean_inc(v_index_1776_);
lean_dec(v_x2_1775_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v_toEnvExtension_1787_; lean_object* v_asyncMode_1788_; uint8_t v_logWrites_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1786_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1787_ = lean_ctor_get(v___x_1786_, 0);
v_asyncMode_1788_ = lean_ctor_get(v_toEnvExtension_1787_, 2);
v_logWrites_1789_ = lean_ctor_get_uint8(v_toEnvExtension_1787_, sizeof(void*)*6);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_declName_1773_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1790_);
v___x_1792_ = v___x_1784_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_index_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_sourceString_1777_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_imports_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_currNamespace_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_openDecls_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_options_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_check_1782_);
v___x_1792_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___f_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1793_, 0, v___x_1786_);
lean_closure_set(v___f_1793_, 1, v___x_1792_);
v___x_1794_ = lean_box(0);
v___x_1795_ = 1;
if (v_logWrites_1789_ == 0)
{
lean_object* v___x_1796_; 
lean_inc_ref(v_toEnvExtension_1787_);
v___x_1796_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1787_, v_x1_1774_, v___f_1793_, v_asyncMode_1788_, v___x_1794_, v___x_1795_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_inc_ref_n(v_toEnvExtension_1787_, 2);
v___x_1797_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1787_, v_x1_1774_);
lean_dec_ref(v_x1_1774_);
v___x_1798_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1787_, v___x_1797_, v___f_1793_, v_asyncMode_1788_, v___x_1794_, v___x_1795_);
return v___x_1798_;
}
}
}
}
}
lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_1821_, lean_object* v_docs_1822_, uint8_t v___x_1823_, lean_object* v_deferred_1824_, lean_object* v___f_1825_, lean_object* v_env_1826_){
_start:
{
lean_object* v___x_1827_; lean_object* v_env_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1827_ = l_Lean_versoDocStringExt;
v_env_1828_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1827_, v_env_1826_, v_declName_1821_, v_docs_1822_, v___x_1823_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_array_get_size(v_deferred_1824_);
v___x_1831_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1832_ = lean_nat_dec_lt(v___x_1829_, v___x_1830_);
if (v___x_1832_ == 0)
{
lean_dec_ref(v___f_1825_);
lean_dec_ref(v_deferred_1824_);
return v_env_1828_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v___x_1830_, v___x_1830_);
if (v___x_1833_ == 0)
{
if (v___x_1832_ == 0)
{
lean_dec_ref(v___f_1825_);
lean_dec_ref(v_deferred_1824_);
return v_env_1828_;
}
else
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = lean_usize_of_nat(v___x_1830_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1831_, v___f_1825_, v_deferred_1824_, v___x_1834_, v___x_1835_, v_env_1828_);
return v___x_1836_;
}
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = lean_usize_of_nat(v___x_1830_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1831_, v___f_1825_, v_deferred_1824_, v___x_1837_, v___x_1838_, v_env_1828_);
return v___x_1839_;
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoDocStringCore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1821_ = stack[0].m_obj;
lean_object* v_docs_1822_ = stack[1].m_obj;
uint8_t v___x_1823_ = stack[2].m_num;
lean_object* v_deferred_1824_ = stack[3].m_obj;
lean_object* v___f_1825_ = stack[4].m_obj;
lean_object* v_env_1826_ = stack[5].m_obj;
lean_object* v_res_1840_;
v_res_1840_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_1821_, v_docs_1822_, v___x_1823_, v_deferred_1824_, v___f_1825_, v_env_1826_);
stack->m_obj
 = v_res_1840_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1841_, lean_object* v_docs_1842_, lean_object* v___x_1843_, lean_object* v_deferred_1844_, lean_object* v___f_1845_, lean_object* v_env_1846_){
_start:
{
uint8_t v___x_406__boxed_1847_; lean_object* v_res_1848_; 
v___x_406__boxed_1847_ = lean_unbox(v___x_1843_);
v_res_1848_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_1841_, v_docs_1842_, v___x_406__boxed_1847_, v_deferred_1844_, v___f_1845_, v_env_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_modifyEnv_1849_, lean_object* v___f_1850_, lean_object* v_____r_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_apply_1(v_modifyEnv_1849_, v___f_1850_);
return v___x_1852_;
}
}
lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object* v_declName_1855_, lean_object* v_modifyEnv_1856_, lean_object* v___f_1857_, uint8_t v___x_1858_, uint8_t v___x_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_toBind_1862_, lean_object* v___f_1863_, lean_object* v_____do__lift_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1864_, v_declName_1855_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v___x_1866_; 
lean_dec(v___f_1863_);
lean_dec(v_toBind_1862_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
lean_dec(v_declName_1855_);
v___x_1866_ = lean_apply_1(v_modifyEnv_1856_, v___f_1857_);
return v___x_1866_;
}
else
{
lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1882_; 
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v___x_1865_, 0);
lean_dec(v_unused_1883_);
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1882_;
goto v_resetjp_1867_;
}
else
{
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1882_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
if (v___x_1858_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_dec_ref(v___f_1857_);
lean_dec(v_modifyEnv_1856_);
v___x_1870_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_1871_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1855_, v___x_1859_);
v___x_1872_ = lean_string_append(v___x_1870_, v___x_1871_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_1874_ = lean_string_append(v___x_1872_, v___x_1873_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 3);
lean_ctor_set(v___x_1868_, 0, v___x_1874_);
v___x_1876_ = v___x_1868_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = l_Lean_MessageData_ofFormat(v___x_1876_);
v___x_1878_ = l_Lean_throwError___redArg(v_inst_1860_, v_inst_1861_, v___x_1877_);
v___x_1879_ = lean_apply_4(v_toBind_1862_, lean_box(0), lean_box(0), v___x_1878_, v___f_1863_);
return v___x_1879_;
}
}
else
{
lean_object* v___x_1881_; 
lean_del_object(v___x_1868_);
lean_dec(v___f_1863_);
lean_dec(v_toBind_1862_);
lean_dec_ref(v_inst_1861_);
lean_dec_ref(v_inst_1860_);
lean_dec(v_declName_1855_);
v___x_1881_ = lean_apply_1(v_modifyEnv_1856_, v___f_1857_);
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoDocStringCore___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1855_ = stack[0].m_obj;
lean_object* v_modifyEnv_1856_ = stack[1].m_obj;
lean_object* v___f_1857_ = stack[2].m_obj;
uint8_t v___x_1858_ = stack[3].m_num;
uint8_t v___x_1859_ = stack[4].m_num;
lean_object* v_inst_1860_ = stack[5].m_obj;
lean_object* v_inst_1861_ = stack[6].m_obj;
lean_object* v_toBind_1862_ = stack[7].m_obj;
lean_object* v___f_1863_ = stack[8].m_obj;
lean_object* v_____do__lift_1864_ = stack[9].m_obj;
lean_object* v_res_1884_;
v_res_1884_ = l_Lean_addVersoDocStringCore___redArg___lam__4(v_declName_1855_, v_modifyEnv_1856_, v___f_1857_, v___x_1858_, v___x_1859_, v_inst_1860_, v_inst_1861_, v_toBind_1862_, v___f_1863_, v_____do__lift_1864_);
stack->m_obj
 = v_res_1884_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object* v_declName_1885_, lean_object* v_modifyEnv_1886_, lean_object* v___f_1887_, lean_object* v___x_1888_, lean_object* v___x_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_toBind_1892_, lean_object* v___f_1893_, lean_object* v_____do__lift_1894_){
_start:
{
uint8_t v___x_504__boxed_1895_; uint8_t v___x_505__boxed_1896_; lean_object* v_res_1897_; 
v___x_504__boxed_1895_ = lean_unbox(v___x_1888_);
v___x_505__boxed_1896_ = lean_unbox(v___x_1889_);
v_res_1897_ = l_Lean_addVersoDocStringCore___redArg___lam__4(v_declName_1885_, v_modifyEnv_1886_, v___f_1887_, v___x_504__boxed_1895_, v___x_505__boxed_1896_, v_inst_1890_, v_inst_1891_, v_toBind_1892_, v___f_1893_, v_____do__lift_1894_);
lean_dec_ref(v_____do__lift_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_declName_1901_, lean_object* v_docs_1902_, lean_object* v_deferred_1903_){
_start:
{
lean_object* v_toApplicative_1904_; lean_object* v_toBind_1905_; lean_object* v_toPure_1906_; uint8_t v___x_1907_; 
v_toApplicative_1904_ = lean_ctor_get(v_inst_1898_, 0);
v_toBind_1905_ = lean_ctor_get(v_inst_1898_, 1);
lean_inc(v_toBind_1905_);
v_toPure_1906_ = lean_ctor_get(v_toApplicative_1904_, 1);
v___x_1907_ = l_Lean_Name_isAnonymous(v_declName_1901_);
if (v___x_1907_ == 0)
{
lean_object* v_getEnv_1908_; lean_object* v_modifyEnv_1909_; lean_object* v___f_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___f_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; 
v_getEnv_1908_ = lean_ctor_get(v_inst_1899_, 0);
lean_inc(v_getEnv_1908_);
v_modifyEnv_1909_ = lean_ctor_get(v_inst_1899_, 1);
lean_inc_n(v_modifyEnv_1909_, 2);
lean_dec_ref(v_inst_1899_);
lean_inc_n(v_declName_1901_, 2);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1910_, 0, v_declName_1901_);
v___x_1911_ = 1;
v___x_1912_ = lean_box(v___x_1911_);
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1913_, 0, v_declName_1901_);
lean_closure_set(v___f_1913_, 1, v_docs_1902_);
lean_closure_set(v___f_1913_, 2, v___x_1912_);
lean_closure_set(v___f_1913_, 3, v_deferred_1903_);
lean_closure_set(v___f_1913_, 4, v___f_1910_);
lean_inc_ref(v___f_1913_);
v___f_1914_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3), 3, 2);
lean_closure_set(v___f_1914_, 0, v_modifyEnv_1909_);
lean_closure_set(v___f_1914_, 1, v___f_1913_);
v___x_1915_ = lean_box(v___x_1907_);
v___x_1916_ = lean_box(v___x_1911_);
lean_inc(v_toBind_1905_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1917_, 0, v_declName_1901_);
lean_closure_set(v___f_1917_, 1, v_modifyEnv_1909_);
lean_closure_set(v___f_1917_, 2, v___f_1913_);
lean_closure_set(v___f_1917_, 3, v___x_1915_);
lean_closure_set(v___f_1917_, 4, v___x_1916_);
lean_closure_set(v___f_1917_, 5, v_inst_1898_);
lean_closure_set(v___f_1917_, 6, v_inst_1900_);
lean_closure_set(v___f_1917_, 7, v_toBind_1905_);
lean_closure_set(v___f_1917_, 8, v___f_1914_);
v___x_1918_ = lean_apply_4(v_toBind_1905_, lean_box(0), lean_box(0), v_getEnv_1908_, v___f_1917_);
return v___x_1918_;
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_inc(v_toPure_1906_);
lean_dec(v_toBind_1905_);
lean_dec_ref(v_deferred_1903_);
lean_dec_ref(v_docs_1902_);
lean_dec(v_declName_1901_);
lean_dec_ref(v_inst_1900_);
lean_dec_ref(v_inst_1899_);
lean_dec_ref(v_inst_1898_);
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_apply_2(v_toPure_1906_, lean_box(0), v___x_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_declName_1926_, lean_object* v_docs_1927_, lean_object* v_deferred_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1922_, v_inst_1923_, v_inst_1925_, v_declName_1926_, v_docs_1927_, v_deferred_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1930_, lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_declName_1935_, lean_object* v_docs_1936_, lean_object* v_deferred_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_addVersoDocStringCore(v_m_1930_, v_inst_1931_, v_inst_1932_, v_inst_1933_, v_inst_1934_, v_declName_1935_, v_docs_1936_, v_deferred_1937_);
lean_dec(v_inst_1933_);
return v_res_1938_;
}
}
lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_size_1939_, uint8_t v___x_1940_, lean_object* v_x1_1941_, lean_object* v_x2_1942_){
_start:
{
lean_object* v_index_1943_; lean_object* v_sourceString_1944_; lean_object* v_imports_1945_; lean_object* v_currNamespace_1946_; lean_object* v_openDecls_1947_; lean_object* v_options_1948_; lean_object* v_check_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1966_; 
v_index_1943_ = lean_ctor_get(v_x2_1942_, 1);
v_sourceString_1944_ = lean_ctor_get(v_x2_1942_, 2);
v_imports_1945_ = lean_ctor_get(v_x2_1942_, 3);
v_currNamespace_1946_ = lean_ctor_get(v_x2_1942_, 4);
v_openDecls_1947_ = lean_ctor_get(v_x2_1942_, 5);
v_options_1948_ = lean_ctor_get(v_x2_1942_, 6);
v_check_1949_ = lean_ctor_get(v_x2_1942_, 7);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_x2_1942_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v_x2_1942_, 0);
lean_dec(v_unused_1967_);
v___x_1951_ = v_x2_1942_;
v_isShared_1952_ = v_isSharedCheck_1966_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_check_1949_);
lean_inc(v_options_1948_);
lean_inc(v_openDecls_1947_);
lean_inc(v_currNamespace_1946_);
lean_inc(v_imports_1945_);
lean_inc(v_sourceString_1944_);
lean_inc(v_index_1943_);
lean_dec(v_x2_1942_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1966_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v_toEnvExtension_1954_; lean_object* v_asyncMode_1955_; uint8_t v_logWrites_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1953_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1954_ = lean_ctor_get(v___x_1953_, 0);
v_asyncMode_1955_ = lean_ctor_get(v_toEnvExtension_1954_, 2);
v_logWrites_1956_ = lean_ctor_get_uint8(v_toEnvExtension_1954_, sizeof(void*)*6);
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_size_1939_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1957_);
v___x_1959_ = v___x_1951_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_index_1943_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_sourceString_1944_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v_imports_1945_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v_currNamespace_1946_);
lean_ctor_set(v_reuseFailAlloc_1965_, 5, v_openDecls_1947_);
lean_ctor_set(v_reuseFailAlloc_1965_, 6, v_options_1948_);
lean_ctor_set(v_reuseFailAlloc_1965_, 7, v_check_1949_);
v___x_1959_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___f_1960_; lean_object* v___x_1961_; 
v___f_1960_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1960_, 0, v___x_1953_);
lean_closure_set(v___f_1960_, 1, v___x_1959_);
v___x_1961_ = lean_box(0);
if (v_logWrites_1956_ == 0)
{
lean_object* v___x_1962_; 
lean_inc_ref(v_toEnvExtension_1954_);
v___x_1962_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1954_, v_x1_1941_, v___f_1960_, v_asyncMode_1955_, v___x_1961_, v___x_1940_);
return v___x_1962_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_inc_ref_n(v_toEnvExtension_1954_, 2);
v___x_1963_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1954_, v_x1_1941_);
lean_dec_ref(v_x1_1941_);
v___x_1964_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1954_, v___x_1963_, v___f_1960_, v_asyncMode_1955_, v___x_1961_, v___x_1940_);
return v___x_1964_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoModDocStringCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_1939_ = stack[0].m_obj;
uint8_t v___x_1940_ = stack[1].m_num;
lean_object* v_x1_1941_ = stack[2].m_obj;
lean_object* v_x2_1942_ = stack[3].m_obj;
lean_object* v_res_1968_;
v_res_1968_ = l_Lean_addVersoModDocStringCore___redArg___lam__1(v_size_1939_, v___x_1940_, v_x1_1941_, v_x2_1942_);
stack->m_obj
 = v_res_1968_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed(lean_object* v_size_1969_, lean_object* v___x_1970_, lean_object* v_x1_1971_, lean_object* v_x2_1972_){
_start:
{
uint8_t v___x_313__boxed_1973_; lean_object* v_res_1974_; 
v___x_313__boxed_1973_ = lean_unbox(v___x_1970_);
v_res_1974_ = l_Lean_addVersoModDocStringCore___redArg___lam__1(v_size_1969_, v___x_313__boxed_1973_, v_x1_1971_, v_x2_1972_);
return v_res_1974_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_deferred_1981_, lean_object* v_inst_1982_, lean_object* v___f_1983_, lean_object* v_____do__lift_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1984_, v_docs_1978_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v___f_1983_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_deferred_1981_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_1988_ = l_Lean_stringToMessageData(v_a_1986_);
v___x_1989_ = l_Lean_indentD(v___x_1988_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_throwError___redArg(v_inst_1979_, v_inst_1980_, v___x_1990_);
return v___x_1991_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
lean_dec_ref(v_inst_1980_);
lean_dec_ref(v_inst_1979_);
v_a_1992_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_array_get_size(v_deferred_1981_);
v___x_1995_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1996_ = lean_nat_dec_lt(v___x_1993_, v___x_1994_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v___f_1983_);
lean_dec_ref(v_deferred_1981_);
v___x_1997_ = l_Lean_setEnv___redArg(v_inst_1982_, v_a_1992_);
return v___x_1997_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_nat_dec_le(v___x_1994_, v___x_1994_);
if (v___x_1998_ == 0)
{
if (v___x_1996_ == 0)
{
lean_object* v___x_1999_; 
lean_dec_ref(v___f_1983_);
lean_dec_ref(v_deferred_1981_);
v___x_1999_ = l_Lean_setEnv___redArg(v_inst_1982_, v_a_1992_);
return v___x_1999_;
}
else
{
size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = lean_usize_of_nat(v___x_1994_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1995_, v___f_1983_, v_deferred_1981_, v___x_2000_, v___x_2001_, v_a_1992_);
v___x_2003_ = l_Lean_setEnv___redArg(v_inst_1982_, v___x_2002_);
return v___x_2003_;
}
}
else
{
size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = lean_usize_of_nat(v___x_1994_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1995_, v___f_1983_, v_deferred_1981_, v___x_2004_, v___x_2005_, v_a_1992_);
v___x_2007_ = l_Lean_setEnv___redArg(v_inst_1982_, v___x_2006_);
return v___x_2007_;
}
}
}
}
}
lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(uint8_t v___x_2008_, lean_object* v_docs_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_deferred_2012_, lean_object* v_inst_2013_, lean_object* v_toBind_2014_, lean_object* v_getEnv_2015_, lean_object* v_____do__lift_2016_){
_start:
{
lean_object* v___x_2017_; lean_object* v_size_2018_; lean_object* v___x_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; 
v___x_2017_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2016_);
v_size_2018_ = lean_ctor_get(v___x_2017_, 2);
lean_inc(v_size_2018_);
lean_dec_ref(v___x_2017_);
v___x_2019_ = lean_box(v___x_2008_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2020_, 0, v_size_2018_);
lean_closure_set(v___f_2020_, 1, v___x_2019_);
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 7, 6);
lean_closure_set(v___f_2021_, 0, v_docs_2009_);
lean_closure_set(v___f_2021_, 1, v_inst_2010_);
lean_closure_set(v___f_2021_, 2, v_inst_2011_);
lean_closure_set(v___f_2021_, 3, v_deferred_2012_);
lean_closure_set(v___f_2021_, 4, v_inst_2013_);
lean_closure_set(v___f_2021_, 5, v___f_2020_);
v___x_2022_ = lean_apply_4(v_toBind_2014_, lean_box(0), lean_box(0), v_getEnv_2015_, v___f_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT void l_Lean_addVersoModDocStringCore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2008_ = stack[0].m_num;
lean_object* v_docs_2009_ = stack[1].m_obj;
lean_object* v_inst_2010_ = stack[2].m_obj;
lean_object* v_inst_2011_ = stack[3].m_obj;
lean_object* v_deferred_2012_ = stack[4].m_obj;
lean_object* v_inst_2013_ = stack[5].m_obj;
lean_object* v_toBind_2014_ = stack[6].m_obj;
lean_object* v_getEnv_2015_ = stack[7].m_obj;
lean_object* v_____do__lift_2016_ = stack[8].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l_Lean_addVersoModDocStringCore___redArg___lam__2(v___x_2008_, v_docs_2009_, v_inst_2010_, v_inst_2011_, v_deferred_2012_, v_inst_2013_, v_toBind_2014_, v_getEnv_2015_, v_____do__lift_2016_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed(lean_object* v___x_2024_, lean_object* v_docs_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_deferred_2028_, lean_object* v_inst_2029_, lean_object* v_toBind_2030_, lean_object* v_getEnv_2031_, lean_object* v_____do__lift_2032_){
_start:
{
uint8_t v___x_488__boxed_2033_; lean_object* v_res_2034_; 
v___x_488__boxed_2033_ = lean_unbox(v___x_2024_);
v_res_2034_ = l_Lean_addVersoModDocStringCore___redArg___lam__2(v___x_488__boxed_2033_, v_docs_2025_, v_inst_2026_, v_inst_2027_, v_deferred_2028_, v_inst_2029_, v_toBind_2030_, v_getEnv_2031_, v_____do__lift_2032_);
return v_res_2034_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_docs_2040_, lean_object* v_deferred_2041_, lean_object* v_inst_2042_, lean_object* v_toBind_2043_, lean_object* v_getEnv_2044_, lean_object* v_____do__lift_2045_){
_start:
{
lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = l_Lean_getMainModuleDoc(v_____do__lift_2045_);
v___x_2047_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2046_);
lean_dec_ref(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_getEnv_2044_);
lean_dec(v_toBind_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v_deferred_2041_);
lean_dec_ref(v_docs_2040_);
v___x_2048_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2049_ = l_Lean_throwError___redArg(v_inst_2038_, v_inst_2039_, v___x_2048_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_box(v___x_2047_);
lean_inc(v_getEnv_2044_);
lean_inc(v_toBind_2043_);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2051_, 0, v___x_2050_);
lean_closure_set(v___f_2051_, 1, v_docs_2040_);
lean_closure_set(v___f_2051_, 2, v_inst_2038_);
lean_closure_set(v___f_2051_, 3, v_inst_2039_);
lean_closure_set(v___f_2051_, 4, v_deferred_2041_);
lean_closure_set(v___f_2051_, 5, v_inst_2042_);
lean_closure_set(v___f_2051_, 6, v_toBind_2043_);
lean_closure_set(v___f_2051_, 7, v_getEnv_2044_);
v___x_2052_ = lean_apply_4(v_toBind_2043_, lean_box(0), lean_box(0), v_getEnv_2044_, v___f_2051_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_docs_2056_, lean_object* v_deferred_2057_){
_start:
{
lean_object* v_toBind_2058_; lean_object* v_getEnv_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; 
v_toBind_2058_ = lean_ctor_get(v_inst_2053_, 1);
lean_inc_n(v_toBind_2058_, 2);
v_getEnv_2059_ = lean_ctor_get(v_inst_2054_, 0);
lean_inc_n(v_getEnv_2059_, 2);
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2060_, 0, v_inst_2053_);
lean_closure_set(v___f_2060_, 1, v_inst_2055_);
lean_closure_set(v___f_2060_, 2, v_docs_2056_);
lean_closure_set(v___f_2060_, 3, v_deferred_2057_);
lean_closure_set(v___f_2060_, 4, v_inst_2054_);
lean_closure_set(v___f_2060_, 5, v_toBind_2058_);
lean_closure_set(v___f_2060_, 6, v_getEnv_2059_);
v___x_2061_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v_getEnv_2059_, v___f_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_docs_2067_, lean_object* v_deferred_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2063_, v_inst_2064_, v_inst_2066_, v_docs_2067_, v_deferred_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_docs_2075_, lean_object* v_deferred_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_addVersoModDocStringCore(v_m_2070_, v_inst_2071_, v_inst_2072_, v_inst_2073_, v_inst_2074_, v_docs_2075_, v_deferred_2076_);
lean_dec(v_inst_2073_);
return v_res_2077_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_box(1);
v___x_2079_ = l_Lean_MessageData_ofFormat(v___x_2078_);
return v___x_2079_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2));
v___x_2084_ = l_Lean_MessageData_ofFormat(v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
return v_x_2085_;
}
else
{
lean_object* v_head_2087_; lean_object* v_tail_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2110_; 
v_head_2087_ = lean_ctor_get(v_x_2086_, 0);
v_tail_2088_ = lean_ctor_get(v_x_2086_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2090_ = v_x_2086_;
v_isShared_2091_ = v_isSharedCheck_2110_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_tail_2088_);
lean_inc(v_head_2087_);
lean_dec(v_x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2110_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_before_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2108_; 
v_before_2092_ = lean_ctor_get(v_head_2087_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_head_2087_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v_head_2087_, 1);
lean_dec(v_unused_2109_);
v___x_2094_ = v_head_2087_;
v_isShared_2095_ = v_isSharedCheck_2108_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_before_2092_);
lean_dec(v_head_2087_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2108_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 7);
lean_ctor_set(v___x_2094_, 1, v___x_2096_);
lean_ctor_set(v___x_2094_, 0, v_x_2085_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_x_2085_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 7);
lean_ctor_set(v___x_2090_, 1, v___x_2099_);
lean_ctor_set(v___x_2090_, 0, v___x_2098_);
v___x_2101_ = v___x_2090_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = l_Lean_MessageData_ofSyntax(v_before_2092_);
v___x_2103_ = l_Lean_indentD(v___x_2102_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2101_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v_x_2085_ = v___x_2104_;
v_x_2086_ = v_tail_2088_;
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
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1));
v___x_2115_ = l_Lean_MessageData_ofFormat(v___x_2114_);
return v___x_2115_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(lean_object* v_msgData_2116_, lean_object* v_macroStack_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2118_);
v___x_2121_ = l_Lean_Elab_pp_macroStack;
v___x_2122_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_2120_, v___x_2121_);
lean_dec_ref(v___x_2120_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v_macroStack_2117_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_msgData_2116_);
return v___x_2123_;
}
else
{
if (lean_obj_tag(v_macroStack_2117_) == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_msgData_2116_);
return v___x_2124_;
}
else
{
lean_object* v_head_2125_; lean_object* v_after_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2141_; 
v_head_2125_ = lean_ctor_get(v_macroStack_2117_, 0);
lean_inc(v_head_2125_);
v_after_2126_ = lean_ctor_get(v_head_2125_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_head_2125_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v_head_2125_, 0);
lean_dec(v_unused_2142_);
v___x_2128_ = v_head_2125_;
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_after_2126_);
lean_dec(v_head_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 7);
lean_ctor_set(v___x_2128_, 1, v___x_2130_);
lean_ctor_set(v___x_2128_, 0, v_msgData_2116_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_msgData_2116_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_msgData_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2133_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_MessageData_ofSyntax(v_after_2126_);
v___x_2136_ = l_Lean_indentD(v___x_2135_);
v_msgData_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2137_, 0, v___x_2134_);
lean_ctor_set(v_msgData_2137_, 1, v___x_2136_);
v___x_2138_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(v_msgData_2137_, v_macroStack_2117_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2116_ = stack[0].m_obj;
lean_object* v_macroStack_2117_ = stack[1].m_obj;
lean_object* v___y_2118_ = stack[2].m_obj;
lean_object* v_res_2143_;
v_res_2143_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2116_, v_macroStack_2117_, v___y_2118_);
stack->m_obj
 = v_res_2143_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2144_, lean_object* v_macroStack_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2144_, v_macroStack_2145_, v___y_2146_);
lean_dec_ref(v___y_2146_);
return v_res_2148_;
}
}
lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_ref_2157_; lean_object* v_macroStack_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
v_ref_2157_ = lean_ctor_get(v___y_2154_, 2);
v_macroStack_2158_ = lean_ctor_get(v___y_2150_, 1);
v___x_2159_ = l_Lean_Elab_getBetterRef(v_ref_2157_, v_macroStack_2158_);
v___x_2160_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2149_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
lean_inc(v_macroStack_2158_);
v___x_2162_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_a_2161_, v_macroStack_2158_, v___y_2154_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2159_);
lean_ctor_set(v___x_2167_, 1, v_a_2163_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set_tag(v___x_2165_, 1);
lean_ctor_set(v___x_2165_, 0, v___x_2167_);
v___x_2169_ = v___x_2165_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2149_ = stack[0].m_obj;
lean_object* v___y_2150_ = stack[1].m_obj;
lean_object* v___y_2151_ = stack[2].m_obj;
lean_object* v___y_2152_ = stack[3].m_obj;
lean_object* v___y_2153_ = stack[4].m_obj;
lean_object* v___y_2154_ = stack[5].m_obj;
lean_object* v___y_2155_ = stack[6].m_obj;
lean_object* v_res_2172_;
v_res_2172_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
stack->m_obj
 = v_res_2172_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0(lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v_s_2184_){
_start:
{
lean_object* v_addEntryFn_2185_; lean_object* v_importedEntries_2186_; lean_object* v_state_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2195_; 
v_addEntryFn_2185_ = lean_ctor_get(v___x_2182_, 3);
lean_inc(v_addEntryFn_2185_);
lean_dec_ref(v___x_2182_);
v_importedEntries_2186_ = lean_ctor_get(v_s_2184_, 0);
v_state_2187_ = lean_ctor_get(v_s_2184_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_s_2184_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2189_ = v_s_2184_;
v_isShared_2190_ = v_isSharedCheck_2195_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_state_2187_);
lean_inc(v_importedEntries_2186_);
lean_dec(v_s_2184_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2195_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_state_2191_; lean_object* v___x_2193_; 
v_state_2191_ = lean_apply_2(v_addEntryFn_2185_, v_state_2187_, v___x_2183_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v_state_2191_);
v___x_2193_ = v___x_2189_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_importedEntries_2186_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_state_2191_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2196_, lean_object* v_as_2197_, size_t v_i_2198_, size_t v_stop_2199_, lean_object* v_b_2200_){
_start:
{
lean_object* v___y_2202_; uint8_t v___x_2206_; 
v___x_2206_ = lean_usize_dec_eq(v_i_2198_, v_stop_2199_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v_index_2208_; lean_object* v_sourceString_2209_; lean_object* v_imports_2210_; lean_object* v_currNamespace_2211_; lean_object* v_openDecls_2212_; lean_object* v_options_2213_; lean_object* v_check_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2232_; 
v___x_2207_ = lean_array_uget(v_as_2197_, v_i_2198_);
v_index_2208_ = lean_ctor_get(v___x_2207_, 1);
v_sourceString_2209_ = lean_ctor_get(v___x_2207_, 2);
v_imports_2210_ = lean_ctor_get(v___x_2207_, 3);
v_currNamespace_2211_ = lean_ctor_get(v___x_2207_, 4);
v_openDecls_2212_ = lean_ctor_get(v___x_2207_, 5);
v_options_2213_ = lean_ctor_get(v___x_2207_, 6);
v_check_2214_ = lean_ctor_get(v___x_2207_, 7);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v___x_2207_, 0);
lean_dec(v_unused_2233_);
v___x_2216_ = v___x_2207_;
v_isShared_2217_ = v_isSharedCheck_2232_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_check_2214_);
lean_inc(v_options_2213_);
lean_inc(v_openDecls_2212_);
lean_inc(v_currNamespace_2211_);
lean_inc(v_imports_2210_);
lean_inc(v_sourceString_2209_);
lean_inc(v_index_2208_);
lean_dec(v___x_2207_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2232_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v_toEnvExtension_2219_; lean_object* v_asyncMode_2220_; uint8_t v_logWrites_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2218_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2219_ = lean_ctor_get(v___x_2218_, 0);
v_asyncMode_2220_ = lean_ctor_get(v_toEnvExtension_2219_, 2);
v_logWrites_2221_ = lean_ctor_get_uint8(v_toEnvExtension_2219_, sizeof(void*)*6);
lean_inc(v_declName_2196_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_declName_2196_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2222_);
v___x_2224_ = v___x_2216_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_index_2208_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_sourceString_2209_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_imports_2210_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_currNamespace_2211_);
lean_ctor_set(v_reuseFailAlloc_2231_, 5, v_openDecls_2212_);
lean_ctor_set(v_reuseFailAlloc_2231_, 6, v_options_2213_);
lean_ctor_set(v_reuseFailAlloc_2231_, 7, v_check_2214_);
v___x_2224_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___f_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___f_2225_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2225_, 0, v___x_2218_);
lean_closure_set(v___f_2225_, 1, v___x_2224_);
v___x_2226_ = lean_box(0);
v___x_2227_ = 1;
if (v_logWrites_2221_ == 0)
{
lean_object* v___x_2228_; 
lean_inc_ref(v_toEnvExtension_2219_);
v___x_2228_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2219_, v_b_2200_, v___f_2225_, v_asyncMode_2220_, v___x_2226_, v___x_2227_);
v___y_2202_ = v___x_2228_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_inc_ref_n(v_toEnvExtension_2219_, 2);
v___x_2229_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2219_, v_b_2200_);
lean_dec_ref(v_b_2200_);
v___x_2230_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2219_, v___x_2229_, v___f_2225_, v_asyncMode_2220_, v___x_2226_, v___x_2227_);
v___y_2202_ = v___x_2230_;
goto v___jp_2201_;
}
}
}
}
else
{
lean_dec(v_declName_2196_);
return v_b_2200_;
}
v___jp_2201_:
{
size_t v___x_2203_; size_t v___x_2204_; 
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_add(v_i_2198_, v___x_2203_);
v_i_2198_ = v___x_2204_;
v_b_2200_ = v___y_2202_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2196_ = stack[0].m_obj;
lean_object* v_as_2197_ = stack[1].m_obj;
size_t v_i_2198_ = stack[2].m_num;
size_t v_stop_2199_ = stack[3].m_num;
lean_object* v_b_2200_ = stack[4].m_obj;
lean_object* v_res_2234_;
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2196_, v_as_2197_, v_i_2198_, v_stop_2199_, v_b_2200_);
stack->m_obj
 = v_res_2234_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2235_, lean_object* v_as_2236_, lean_object* v_i_2237_, lean_object* v_stop_2238_, lean_object* v_b_2239_){
_start:
{
size_t v_i_boxed_2240_; size_t v_stop_boxed_2241_; lean_object* v_res_2242_; 
v_i_boxed_2240_ = lean_unbox_usize(v_i_2237_);
lean_dec(v_i_2237_);
v_stop_boxed_2241_ = lean_unbox_usize(v_stop_2238_);
lean_dec(v_stop_2238_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2235_, v_as_2236_, v_i_boxed_2240_, v_stop_boxed_2241_, v_b_2239_);
lean_dec_ref(v_as_2236_);
return v_res_2242_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2248_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
lean_ctor_set(v___x_2248_, 2, v___x_2247_);
lean_ctor_set(v___x_2248_, 3, v___x_2247_);
lean_ctor_set(v___x_2248_, 4, v___x_2247_);
lean_ctor_set(v___x_2248_, 5, v___x_2247_);
return v___x_2248_;
}
}
lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2249_, lean_object* v_docs_2250_, lean_object* v_deferred_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; uint8_t v___x_2291_; 
v___x_2291_ = l_Lean_Name_isAnonymous(v_declName_2249_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___x_2314_; lean_object* v_env_2315_; lean_object* v___x_2316_; 
v___x_2292_ = 1;
v___x_2314_ = lean_st_ref_get(v___y_2257_);
v_env_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_ref(v_env_2315_);
lean_dec(v___x_2314_);
v___x_2316_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2315_, v_declName_2249_);
lean_dec_ref(v_env_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
v___y_2294_ = v___y_2255_;
v___y_2295_ = v___y_2257_;
goto v___jp_2293_;
}
else
{
lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2330_; 
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v___x_2316_, 0);
lean_dec(v_unused_2331_);
v___x_2318_ = v___x_2316_;
v_isShared_2319_ = v_isSharedCheck_2330_;
goto v_resetjp_2317_;
}
else
{
lean_dec(v___x_2316_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2330_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (v___x_2291_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
lean_dec_ref(v_docs_2250_);
v___x_2320_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2249_, v___x_2292_);
v___x_2322_ = lean_string_append(v___x_2320_, v___x_2321_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2324_ = lean_string_append(v___x_2322_, v___x_2323_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 3);
lean_ctor_set(v___x_2318_, 0, v___x_2324_);
v___x_2326_ = v___x_2318_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = l_Lean_MessageData_ofFormat(v___x_2326_);
v___x_2328_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2327_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2328_;
}
}
else
{
lean_del_object(v___x_2318_);
v___y_2294_ = v___y_2255_;
v___y_2295_ = v___y_2257_;
goto v___jp_2293_;
}
}
}
v___jp_2293_:
{
lean_object* v___x_2296_; lean_object* v_env_2297_; lean_object* v_nextMacroScope_2298_; lean_object* v_ngen_2299_; lean_object* v_auxDeclNGen_2300_; lean_object* v_traceState_2301_; lean_object* v_recordedDeps_2302_; lean_object* v_messages_2303_; lean_object* v_infoState_2304_; lean_object* v_snapshotTasks_2305_; lean_object* v___x_2306_; lean_object* v_env_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2296_ = lean_st_ref_take(v___y_2295_);
v_env_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc_ref(v_env_2297_);
v_nextMacroScope_2298_ = lean_ctor_get(v___x_2296_, 1);
lean_inc(v_nextMacroScope_2298_);
v_ngen_2299_ = lean_ctor_get(v___x_2296_, 2);
lean_inc_ref(v_ngen_2299_);
v_auxDeclNGen_2300_ = lean_ctor_get(v___x_2296_, 3);
lean_inc_ref(v_auxDeclNGen_2300_);
v_traceState_2301_ = lean_ctor_get(v___x_2296_, 4);
lean_inc_ref(v_traceState_2301_);
v_recordedDeps_2302_ = lean_ctor_get(v___x_2296_, 6);
lean_inc_ref(v_recordedDeps_2302_);
v_messages_2303_ = lean_ctor_get(v___x_2296_, 7);
lean_inc_ref(v_messages_2303_);
v_infoState_2304_ = lean_ctor_get(v___x_2296_, 8);
lean_inc_ref(v_infoState_2304_);
v_snapshotTasks_2305_ = lean_ctor_get(v___x_2296_, 9);
lean_inc_ref(v_snapshotTasks_2305_);
lean_dec(v___x_2296_);
v___x_2306_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2249_);
v_env_2307_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2306_, v_env_2297_, v_declName_2249_, v_docs_2250_, v___x_2292_);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = lean_array_get_size(v_deferred_2251_);
v___x_2310_ = lean_nat_dec_lt(v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_dec(v_declName_2249_);
v___y_2260_ = v___y_2294_;
v___y_2261_ = v_snapshotTasks_2305_;
v___y_2262_ = v_traceState_2301_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v_recordedDeps_2302_;
v___y_2265_ = v_nextMacroScope_2298_;
v___y_2266_ = v_infoState_2304_;
v___y_2267_ = v_auxDeclNGen_2300_;
v___y_2268_ = v_ngen_2299_;
v___y_2269_ = v_messages_2303_;
v___y_2270_ = v_env_2307_;
goto v___jp_2259_;
}
else
{
size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = lean_usize_of_nat(v___x_2309_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2249_, v_deferred_2251_, v___x_2311_, v___x_2312_, v_env_2307_);
v___y_2260_ = v___y_2294_;
v___y_2261_ = v_snapshotTasks_2305_;
v___y_2262_ = v_traceState_2301_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v_recordedDeps_2302_;
v___y_2265_ = v_nextMacroScope_2298_;
v___y_2266_ = v_infoState_2304_;
v___y_2267_ = v_auxDeclNGen_2300_;
v___y_2268_ = v_ngen_2299_;
v___y_2269_ = v_messages_2303_;
v___y_2270_ = v___x_2313_;
goto v___jp_2259_;
}
}
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_docs_2250_);
lean_dec(v_declName_2249_);
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
v___jp_2259_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_mctx_2275_; lean_object* v_zetaDeltaFVarIds_2276_; lean_object* v_postponed_2277_; lean_object* v_diag_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2289_; 
v___x_2271_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2272_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2272_, 0, v___y_2270_);
lean_ctor_set(v___x_2272_, 1, v___y_2265_);
lean_ctor_set(v___x_2272_, 2, v___y_2268_);
lean_ctor_set(v___x_2272_, 3, v___y_2267_);
lean_ctor_set(v___x_2272_, 4, v___y_2262_);
lean_ctor_set(v___x_2272_, 5, v___x_2271_);
lean_ctor_set(v___x_2272_, 6, v___y_2264_);
lean_ctor_set(v___x_2272_, 7, v___y_2269_);
lean_ctor_set(v___x_2272_, 8, v___y_2266_);
lean_ctor_set(v___x_2272_, 9, v___y_2261_);
v___x_2273_ = lean_st_ref_put(v___y_2263_, v___x_2272_);
v___x_2274_ = lean_st_ref_take(v___y_2260_);
v_mctx_2275_ = lean_ctor_get(v___x_2274_, 0);
v_zetaDeltaFVarIds_2276_ = lean_ctor_get(v___x_2274_, 2);
v_postponed_2277_ = lean_ctor_get(v___x_2274_, 3);
v_diag_2278_ = lean_ctor_get(v___x_2274_, 4);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v___x_2274_, 1);
lean_dec(v_unused_2290_);
v___x_2280_ = v___x_2274_;
v_isShared_2281_ = v_isSharedCheck_2289_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_diag_2278_);
lean_inc(v_postponed_2277_);
lean_inc(v_zetaDeltaFVarIds_2276_);
lean_inc(v_mctx_2275_);
lean_dec(v___x_2274_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2289_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v___x_2283_);
v___x_2285_ = v___x_2280_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_mctx_2275_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_zetaDeltaFVarIds_2276_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_postponed_2277_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_diag_2278_);
v___x_2285_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_st_ref_put(v___y_2260_, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2282_);
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2249_ = stack[0].m_obj;
lean_object* v_docs_2250_ = stack[1].m_obj;
lean_object* v_deferred_2251_ = stack[2].m_obj;
lean_object* v___y_2252_ = stack[3].m_obj;
lean_object* v___y_2253_ = stack[4].m_obj;
lean_object* v___y_2254_ = stack[5].m_obj;
lean_object* v___y_2255_ = stack[6].m_obj;
lean_object* v___y_2256_ = stack[7].m_obj;
lean_object* v___y_2257_ = stack[8].m_obj;
lean_object* v_res_2334_;
v_res_2334_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2249_, v_docs_2250_, v_deferred_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
stack->m_obj
 = v_res_2334_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2335_, lean_object* v_docs_2336_, lean_object* v_deferred_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2335_, v_docs_2336_, v_deferred_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec_ref(v_deferred_2337_);
return v_res_2345_;
}
}
lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2346_, lean_object* v_binders_2347_, lean_object* v_docComment_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___x_2376_; lean_object* v_env_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_st_ref_get(v_a_2354_);
v_env_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc_ref(v_env_2377_);
lean_dec(v___x_2376_);
v___x_2378_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2377_, v_declName_2346_);
lean_dec_ref(v_env_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
v___y_2357_ = v_a_2349_;
v___y_2358_ = v_a_2350_;
v___y_2359_ = v_a_2351_;
v___y_2360_ = v_a_2352_;
v___y_2361_ = v_a_2353_;
v___y_2362_ = v_a_2354_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_binders_2347_);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2378_, 0);
lean_dec(v_unused_2394_);
v___x_2380_ = v___x_2378_;
v_isShared_2381_ = v_isSharedCheck_2393_;
goto v_resetjp_2379_;
}
else
{
lean_dec(v___x_2378_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2393_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2382_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2383_ = 1;
v___x_2384_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2346_, v___x_2383_);
v___x_2385_ = lean_string_append(v___x_2382_, v___x_2384_);
lean_dec_ref(v___x_2384_);
v___x_2386_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2387_ = lean_string_append(v___x_2385_, v___x_2386_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 3);
lean_ctor_set(v___x_2380_, 0, v___x_2387_);
v___x_2389_ = v___x_2380_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = l_Lean_MessageData_ofFormat(v___x_2389_);
v___x_2391_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2390_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v___x_2391_;
}
}
}
v___jp_2356_:
{
lean_object* v___x_2363_; 
lean_inc(v_declName_2346_);
v___x_2363_ = l_Lean_versoDocString(v_declName_2346_, v_binders_2347_, v_docComment_2348_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v_toVersoDocString_2365_; lean_object* v_deferredChecks_2366_; lean_object* v___x_2367_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_toVersoDocString_2365_ = lean_ctor_get(v_a_2364_, 0);
lean_inc_ref(v_toVersoDocString_2365_);
v_deferredChecks_2366_ = lean_ctor_get(v_a_2364_, 1);
lean_inc_ref(v_deferredChecks_2366_);
lean_dec(v_a_2364_);
v___x_2367_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2346_, v_toVersoDocString_2365_, v_deferredChecks_2366_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec_ref(v_deferredChecks_2366_);
return v___x_2367_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_declName_2346_);
v_a_2368_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2363_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2363_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2346_ = stack[0].m_obj;
lean_object* v_binders_2347_ = stack[1].m_obj;
lean_object* v_docComment_2348_ = stack[2].m_obj;
lean_object* v_a_2349_ = stack[3].m_obj;
lean_object* v_a_2350_ = stack[4].m_obj;
lean_object* v_a_2351_ = stack[5].m_obj;
lean_object* v_a_2352_ = stack[6].m_obj;
lean_object* v_a_2353_ = stack[7].m_obj;
lean_object* v_a_2354_ = stack[8].m_obj;
lean_object* v_res_2395_;
v_res_2395_ = l_Lean_addVersoDocString(v_declName_2346_, v_binders_2347_, v_docComment_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
stack->m_obj
 = v_res_2395_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2396_, lean_object* v_binders_2397_, lean_object* v_docComment_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_addVersoDocString(v_declName_2396_, v_binders_2397_, v_docComment_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_docComment_2398_);
return v_res_2406_;
}
}
lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2407_, lean_object* v_msg_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_addVersoDocString_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2408_ = stack[1].m_obj;
lean_object* v___y_2409_ = stack[2].m_obj;
lean_object* v___y_2410_ = stack[3].m_obj;
lean_object* v___y_2411_ = stack[4].m_obj;
lean_object* v___y_2412_ = stack[5].m_obj;
lean_object* v___y_2413_ = stack[6].m_obj;
lean_object* v___y_2414_ = stack[7].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_box(0), v_msg_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_msg_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2418_, v_msg_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2427_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(lean_object* v_msgData_2428_, lean_object* v_macroStack_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2428_, v_macroStack_2429_, v___y_2434_);
return v___x_2437_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2428_ = stack[0].m_obj;
lean_object* v_macroStack_2429_ = stack[1].m_obj;
lean_object* v___y_2430_ = stack[2].m_obj;
lean_object* v___y_2431_ = stack[3].m_obj;
lean_object* v___y_2432_ = stack[4].m_obj;
lean_object* v___y_2433_ = stack[5].m_obj;
lean_object* v___y_2434_ = stack[6].m_obj;
lean_object* v___y_2435_ = stack[7].m_obj;
lean_object* v_res_2438_;
v_res_2438_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(v_msgData_2428_, v_macroStack_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
stack->m_obj
 = v_res_2438_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___boxed(lean_object* v_msgData_2439_, lean_object* v_macroStack_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(v_msgData_2439_, v_macroStack_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2448_;
}
}
lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2449_, lean_object* v_docComment_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___x_2478_; lean_object* v_env_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_st_ref_get(v_a_2456_);
v_env_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc_ref(v_env_2479_);
lean_dec(v___x_2478_);
v___x_2480_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2479_, v_declName_2449_);
lean_dec_ref(v_env_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
v___y_2459_ = v_a_2451_;
v___y_2460_ = v_a_2452_;
v___y_2461_ = v_a_2453_;
v___y_2462_ = v_a_2454_;
v___y_2463_ = v_a_2455_;
v___y_2464_ = v_a_2456_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2495_; 
lean_dec_ref(v_docComment_2450_);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2480_, 0);
lean_dec(v_unused_2496_);
v___x_2482_ = v___x_2480_;
v_isShared_2483_ = v_isSharedCheck_2495_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v___x_2480_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2495_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2484_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2485_ = 1;
v___x_2486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2449_, v___x_2485_);
v___x_2487_ = lean_string_append(v___x_2484_, v___x_2486_);
lean_dec_ref(v___x_2486_);
v___x_2488_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2489_ = lean_string_append(v___x_2487_, v___x_2488_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 3);
lean_ctor_set(v___x_2482_, 0, v___x_2489_);
v___x_2491_ = v___x_2482_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = l_Lean_MessageData_ofFormat(v___x_2491_);
v___x_2493_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2492_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
return v___x_2493_;
}
}
}
v___jp_2458_:
{
lean_object* v___x_2465_; 
lean_inc(v_declName_2449_);
v___x_2465_ = l_Lean_versoDocStringFromString(v_declName_2449_, v_docComment_2450_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v_toVersoDocString_2467_; lean_object* v_deferredChecks_2468_; lean_object* v___x_2469_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v_toVersoDocString_2467_ = lean_ctor_get(v_a_2466_, 0);
lean_inc_ref(v_toVersoDocString_2467_);
v_deferredChecks_2468_ = lean_ctor_get(v_a_2466_, 1);
lean_inc_ref(v_deferredChecks_2468_);
lean_dec(v_a_2466_);
v___x_2469_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2449_, v_toVersoDocString_2467_, v_deferredChecks_2468_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec_ref(v_deferredChecks_2468_);
return v___x_2469_;
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v_declName_2449_);
v_a_2470_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2465_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2465_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoDocStringFromString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2449_ = stack[0].m_obj;
lean_object* v_docComment_2450_ = stack[1].m_obj;
lean_object* v_a_2451_ = stack[2].m_obj;
lean_object* v_a_2452_ = stack[3].m_obj;
lean_object* v_a_2453_ = stack[4].m_obj;
lean_object* v_a_2454_ = stack[5].m_obj;
lean_object* v_a_2455_ = stack[6].m_obj;
lean_object* v_a_2456_ = stack[7].m_obj;
lean_object* v_res_2497_;
v_res_2497_ = l_Lean_addVersoDocStringFromString(v_declName_2449_, v_docComment_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
stack->m_obj
 = v_res_2497_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2498_, lean_object* v_docComment_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_addVersoDocStringFromString(v_declName_2498_, v_docComment_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
return v_res_2507_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2508_, lean_object* v_msgData_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = 2;
v___x_2516_ = 0;
v___x_2517_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2508_, v_msgData_2509_, v___x_2515_, v___x_2516_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2517_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2508_ = stack[0].m_obj;
lean_object* v_msgData_2509_ = stack[1].m_obj;
lean_object* v___y_2510_ = stack[2].m_obj;
lean_object* v___y_2511_ = stack[3].m_obj;
lean_object* v___y_2512_ = stack[4].m_obj;
lean_object* v___y_2513_ = stack[5].m_obj;
lean_object* v_res_2518_;
v_res_2518_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2508_, v_msgData_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
stack->m_obj
 = v_res_2518_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2519_, lean_object* v_msgData_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2519_, v_msgData_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v_ref_2519_);
return v_res_2526_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2527_, lean_object* v_str_2528_, lean_object* v_as_2529_, size_t v_sz_2530_, size_t v_i_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_a_2541_; uint8_t v___x_2545_; 
v___x_2545_ = lean_usize_dec_lt(v_i_2531_, v_sz_2530_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_b_2532_);
return v___x_2546_;
}
else
{
lean_object* v_a_2547_; lean_object* v_fst_2548_; lean_object* v_snd_2549_; lean_object* v_start_2550_; lean_object* v_stop_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2571_; 
v_a_2547_ = lean_array_uget_borrowed(v_as_2529_, v_i_2531_);
v_fst_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_fst_2548_);
v_snd_2549_ = lean_ctor_get(v_a_2547_, 1);
v_start_2550_ = lean_ctor_get(v_fst_2548_, 0);
v_stop_2551_ = lean_ctor_get(v_fst_2548_, 1);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_fst_2548_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2553_ = v_fst_2548_;
v_isShared_2554_ = v_isSharedCheck_2571_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_stop_2551_);
lean_inc(v_start_2550_);
lean_dec(v_fst_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2571_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_box(0);
if (lean_obj_tag(v___y_2527_) == 1)
{
lean_object* v_val_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v_val_2556_ = lean_ctor_get(v___y_2527_, 0);
v___x_2557_ = lean_nat_add(v_val_2556_, v_start_2550_);
v___x_2558_ = lean_nat_add(v_val_2556_, v_stop_2551_);
v___x_2559_ = 0;
v___x_2560_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2560_, 0, v___x_2557_);
lean_ctor_set(v___x_2560_, 1, v___x_2558_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*2, v___x_2559_);
v___x_2561_ = lean_string_utf8_extract(v_str_2528_, v_start_2550_, v_stop_2551_);
lean_dec(v_stop_2551_);
lean_dec(v_start_2550_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set_tag(v___x_2553_, 2);
lean_ctor_set(v___x_2553_, 1, v___x_2561_);
lean_ctor_set(v___x_2553_, 0, v___x_2560_);
v___x_2563_ = v___x_2553_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_inc(v_snd_2549_);
v___x_2564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_snd_2549_);
v___x_2565_ = l_Lean_MessageData_ofFormat(v___x_2564_);
v___x_2566_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2563_, v___x_2565_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v___x_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_dec_ref_known(v___x_2566_, 1);
v_a_2541_ = v___x_2555_;
goto v___jp_2540_;
}
else
{
return v___x_2566_;
}
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_del_object(v___x_2553_);
lean_dec(v_stop_2551_);
lean_dec(v_start_2550_);
lean_inc(v_snd_2549_);
v___x_2568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_snd_2549_);
v___x_2569_ = l_Lean_MessageData_ofFormat(v___x_2568_);
v___x_2570_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2569_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_dec_ref_known(v___x_2570_, 1);
v_a_2541_ = v___x_2555_;
goto v___jp_2540_;
}
else
{
return v___x_2570_;
}
}
}
}
v___jp_2540_:
{
size_t v___x_2542_; size_t v___x_2543_; 
v___x_2542_ = ((size_t)1ULL);
v___x_2543_ = lean_usize_add(v_i_2531_, v___x_2542_);
v_i_2531_ = v___x_2543_;
v_b_2532_ = v_a_2541_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2527_ = stack[0].m_obj;
lean_object* v_str_2528_ = stack[1].m_obj;
lean_object* v_as_2529_ = stack[2].m_obj;
size_t v_sz_2530_ = stack[3].m_num;
size_t v_i_2531_ = stack[4].m_num;
lean_object* v_b_2532_ = stack[5].m_obj;
lean_object* v___y_2533_ = stack[6].m_obj;
lean_object* v___y_2534_ = stack[7].m_obj;
lean_object* v___y_2535_ = stack[8].m_obj;
lean_object* v___y_2536_ = stack[9].m_obj;
lean_object* v___y_2537_ = stack[10].m_obj;
lean_object* v___y_2538_ = stack[11].m_obj;
lean_object* v_res_2572_;
v_res_2572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2527_, v_str_2528_, v_as_2529_, v_sz_2530_, v_i_2531_, v_b_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
stack->m_obj
 = v_res_2572_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2573_, lean_object* v_str_2574_, lean_object* v_as_2575_, lean_object* v_sz_2576_, lean_object* v_i_2577_, lean_object* v_b_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
size_t v_sz_boxed_2586_; size_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_sz_boxed_2586_ = lean_unbox_usize(v_sz_2576_);
lean_dec(v_sz_2576_);
v_i_boxed_2587_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2573_, v_str_2574_, v_as_2575_, v_sz_boxed_2586_, v_i_boxed_2587_, v_b_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v_as_2575_);
lean_dec_ref(v_str_2574_);
lean_dec(v___y_2573_);
return v_res_2588_;
}
}
lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_str_2597_; lean_object* v___y_2599_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_str_2597_ = l_Lean_TSyntax_getDocString(v_docstring_2589_);
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = l_Lean_Syntax_getArg(v_docstring_2589_, v___x_2614_);
v___x_2616_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2615_);
lean_dec(v___x_2615_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_box(0);
v___y_2599_ = v___x_2617_;
goto v___jp_2598_;
}
else
{
lean_object* v_val_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; 
v_val_2618_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_val_2618_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2619_ = 0;
v___x_2620_ = l_Lean_SourceInfo_getPos_x3f(v_val_2618_, v___x_2619_);
lean_dec(v_val_2618_);
v___y_2599_ = v___x_2620_;
goto v___jp_2598_;
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v_fst_2601_; lean_object* v___x_2602_; size_t v_sz_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
lean_inc_ref(v_str_2597_);
v___x_2600_ = l_Lean_rewriteManualLinksCore(v_str_2597_);
v_fst_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_fst_2601_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = lean_box(0);
v_sz_2603_ = lean_array_size(v_fst_2601_);
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2599_, v_str_2597_, v_fst_2601_, v_sz_2603_, v___x_2604_, v___x_2602_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_str_2597_);
lean_dec(v___y_2599_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; 
v_unused_2613_ = lean_ctor_get(v___x_2605_, 0);
lean_dec(v_unused_2613_);
v___x_2607_ = v___x_2605_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_dec(v___x_2605_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2602_);
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2602_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
else
{
return v___x_2605_;
}
}
}
}
LEAN_EXPORT void l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_docstring_2589_ = stack[0].m_obj;
lean_object* v___y_2590_ = stack[1].m_obj;
lean_object* v___y_2591_ = stack[2].m_obj;
lean_object* v___y_2592_ = stack[3].m_obj;
lean_object* v___y_2593_ = stack[4].m_obj;
lean_object* v___y_2594_ = stack[5].m_obj;
lean_object* v___y_2595_ = stack[6].m_obj;
lean_object* v_res_2621_;
v_res_2621_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
stack->m_obj
 = v_res_2621_;
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v_docstring_2622_);
return v_res_2630_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2631_, lean_object* v_msg_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_toCold_2640_; lean_object* v_currRecDepth_2641_; lean_object* v_ref_2642_; uint16_t v_optionFlags_2643_; uint8_t v_suppressElabErrors_2644_; uint8_t v_isRecordingDeps_2645_; lean_object* v_ref_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_toCold_2640_ = lean_ctor_get(v___y_2637_, 0);
v_currRecDepth_2641_ = lean_ctor_get(v___y_2637_, 1);
v_ref_2642_ = lean_ctor_get(v___y_2637_, 2);
v_optionFlags_2643_ = lean_ctor_get_uint16(v___y_2637_, sizeof(void*)*3);
v_suppressElabErrors_2644_ = lean_ctor_get_uint8(v___y_2637_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2645_ = lean_ctor_get_uint8(v___y_2637_, sizeof(void*)*3 + 3);
v_ref_2646_ = l_Lean_replaceRef(v_ref_2631_, v_ref_2642_);
lean_inc(v_currRecDepth_2641_);
lean_inc_ref(v_toCold_2640_);
v___x_2647_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2647_, 0, v_toCold_2640_);
lean_ctor_set(v___x_2647_, 1, v_currRecDepth_2641_);
lean_ctor_set(v___x_2647_, 2, v_ref_2646_);
lean_ctor_set_uint16(v___x_2647_, sizeof(void*)*3, v_optionFlags_2643_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*3 + 2, v_suppressElabErrors_2644_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*3 + 3, v_isRecordingDeps_2645_);
v___x_2648_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___x_2647_, v___y_2638_);
lean_dec_ref_known(v___x_2647_, 3);
return v___x_2648_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2631_ = stack[0].m_obj;
lean_object* v_msg_2632_ = stack[1].m_obj;
lean_object* v___y_2633_ = stack[2].m_obj;
lean_object* v___y_2634_ = stack[3].m_obj;
lean_object* v___y_2635_ = stack[4].m_obj;
lean_object* v___y_2636_ = stack[5].m_obj;
lean_object* v___y_2637_ = stack[6].m_obj;
lean_object* v___y_2638_ = stack[7].m_obj;
lean_object* v_res_2649_;
v_res_2649_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2631_, v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
stack->m_obj
 = v_res_2649_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2650_, lean_object* v_msg_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2650_, v_msg_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v_ref_2650_);
return v_res_2659_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_unsigned_to_nat(1u);
v___x_2679_ = l_Lean_Syntax_getArg(v_stx_2664_, v___x_2678_);
if (lean_obj_tag(v___x_2679_) == 1)
{
lean_object* v_kind_2680_; 
v_kind_2680_ = lean_ctor_get(v___x_2679_, 1);
lean_inc(v_kind_2680_);
if (lean_obj_tag(v_kind_2680_) == 1)
{
lean_object* v_pre_2681_; 
v_pre_2681_ = lean_ctor_get(v_kind_2680_, 0);
lean_inc(v_pre_2681_);
if (lean_obj_tag(v_pre_2681_) == 1)
{
lean_object* v_pre_2682_; 
v_pre_2682_ = lean_ctor_get(v_pre_2681_, 0);
lean_inc(v_pre_2682_);
if (lean_obj_tag(v_pre_2682_) == 1)
{
lean_object* v_pre_2683_; 
v_pre_2683_ = lean_ctor_get(v_pre_2682_, 0);
lean_inc(v_pre_2683_);
if (lean_obj_tag(v_pre_2683_) == 1)
{
lean_object* v_pre_2684_; 
v_pre_2684_ = lean_ctor_get(v_pre_2683_, 0);
if (lean_obj_tag(v_pre_2684_) == 0)
{
lean_object* v_args_2685_; lean_object* v_str_2686_; lean_object* v_str_2687_; lean_object* v_str_2688_; lean_object* v_str_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v_args_2685_ = lean_ctor_get(v___x_2679_, 2);
lean_inc_ref(v_args_2685_);
lean_dec_ref_known(v___x_2679_, 3);
v_str_2686_ = lean_ctor_get(v_kind_2680_, 1);
lean_inc_ref(v_str_2686_);
lean_dec_ref_known(v_kind_2680_, 2);
v_str_2687_ = lean_ctor_get(v_pre_2681_, 1);
lean_inc_ref(v_str_2687_);
lean_dec_ref_known(v_pre_2681_, 2);
v_str_2688_ = lean_ctor_get(v_pre_2682_, 1);
lean_inc_ref(v_str_2688_);
lean_dec_ref_known(v_pre_2682_, 2);
v_str_2689_ = lean_ctor_get(v_pre_2683_, 1);
lean_inc_ref(v_str_2689_);
lean_dec_ref_known(v_pre_2683_, 2);
v___x_2690_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2691_ = lean_string_dec_eq(v_str_2689_, v___x_2690_);
lean_dec_ref(v_str_2689_);
if (v___x_2691_ == 0)
{
lean_dec_ref(v_str_2688_);
lean_dec_ref(v_str_2687_);
lean_dec_ref(v_str_2686_);
lean_dec_ref(v_args_2685_);
goto v___jp_2672_;
}
else
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2693_ = lean_string_dec_eq(v_str_2688_, v___x_2692_);
lean_dec_ref(v_str_2688_);
if (v___x_2693_ == 0)
{
lean_dec_ref(v_str_2687_);
lean_dec_ref(v_str_2686_);
lean_dec_ref(v_args_2685_);
goto v___jp_2672_;
}
else
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2695_ = lean_string_dec_eq(v_str_2687_, v___x_2694_);
lean_dec_ref(v_str_2687_);
if (v___x_2695_ == 0)
{
lean_dec_ref(v_str_2686_);
lean_dec_ref(v_args_2685_);
goto v___jp_2672_;
}
else
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2697_ = lean_string_dec_eq(v_str_2686_, v___x_2696_);
lean_dec_ref(v_str_2686_);
if (v___x_2697_ == 0)
{
lean_dec_ref(v_args_2685_);
goto v___jp_2672_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2698_ = lean_array_get_size(v_args_2685_);
v___x_2699_ = lean_unsigned_to_nat(2u);
v___x_2700_ = lean_nat_dec_eq(v___x_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_dec_ref(v_args_2685_);
goto v___jp_2672_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_array_fget(v_args_2685_, v___x_2701_);
lean_dec_ref(v_args_2685_);
if (lean_obj_tag(v___x_2702_) == 2)
{
lean_object* v_val_2703_; lean_object* v___x_2704_; 
lean_dec(v_stx_2664_);
v_val_2703_ = lean_ctor_get(v___x_2702_, 1);
lean_inc_ref(v_val_2703_);
lean_dec_ref_known(v___x_2702_, 2);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_val_2703_);
return v___x_2704_;
}
else
{
lean_dec(v___x_2702_);
goto v___jp_2672_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2683_, 2);
lean_dec_ref_known(v_pre_2682_, 2);
lean_dec_ref_known(v_pre_2681_, 2);
lean_dec_ref_known(v_kind_2680_, 2);
lean_dec_ref_known(v___x_2679_, 3);
goto v___jp_2672_;
}
}
else
{
lean_dec(v_pre_2683_);
lean_dec_ref_known(v_pre_2682_, 2);
lean_dec_ref_known(v_pre_2681_, 2);
lean_dec_ref_known(v_kind_2680_, 2);
lean_dec_ref_known(v___x_2679_, 3);
goto v___jp_2672_;
}
}
else
{
lean_dec(v_pre_2682_);
lean_dec_ref_known(v_pre_2681_, 2);
lean_dec_ref_known(v_kind_2680_, 2);
lean_dec_ref_known(v___x_2679_, 3);
goto v___jp_2672_;
}
}
else
{
lean_dec_ref_known(v_kind_2680_, 2);
lean_dec(v_pre_2681_);
lean_dec_ref_known(v___x_2679_, 3);
goto v___jp_2672_;
}
}
else
{
lean_dec_ref_known(v___x_2679_, 3);
lean_dec(v_kind_2680_);
goto v___jp_2672_;
}
}
else
{
lean_dec(v___x_2679_);
goto v___jp_2672_;
}
v___jp_2672_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2673_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2664_);
v___x_2674_ = l_Lean_MessageData_ofSyntax(v_stx_2664_);
v___x_2675_ = l_Lean_indentD(v___x_2674_);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2673_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2664_, v___x_2676_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v_stx_2664_);
return v___x_2677_;
}
}
}
LEAN_EXPORT void l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2664_ = stack[0].m_obj;
lean_object* v___y_2665_ = stack[1].m_obj;
lean_object* v___y_2666_ = stack[2].m_obj;
lean_object* v___y_2667_ = stack[3].m_obj;
lean_object* v___y_2668_ = stack[4].m_obj;
lean_object* v___y_2669_ = stack[5].m_obj;
lean_object* v___y_2670_ = stack[6].m_obj;
lean_object* v_res_2705_;
v_res_2705_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
stack->m_obj
 = v_res_2705_;
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2714_;
}
}
lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2715_, lean_object* v_docComment_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = l_Lean_Name_isAnonymous(v_declName_2715_);
if (v___x_2724_ == 0)
{
uint8_t v___x_2725_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___x_2790_; lean_object* v_env_2791_; lean_object* v___x_2792_; 
v___x_2725_ = 1;
v___x_2790_ = lean_st_ref_get(v___y_2722_);
v_env_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc_ref(v_env_2791_);
lean_dec(v___x_2790_);
v___x_2792_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2791_, v_declName_2715_);
lean_dec_ref(v_env_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
v___y_2727_ = v___y_2717_;
v___y_2728_ = v___y_2718_;
v___y_2729_ = v___y_2719_;
v___y_2730_ = v___y_2720_;
v___y_2731_ = v___y_2721_;
v___y_2732_ = v___y_2722_;
goto v___jp_2726_;
}
else
{
lean_dec_ref_known(v___x_2792_, 1);
if (v___x_2724_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec(v_docComment_2716_);
v___x_2793_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2794_ = l_Lean_MessageData_ofConstName(v_declName_2715_, v___x_2724_);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2797_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2798_;
}
else
{
v___y_2727_ = v___y_2717_;
v___y_2728_ = v___y_2718_;
v___y_2729_ = v___y_2719_;
v___y_2730_ = v___y_2720_;
v___y_2731_ = v___y_2721_;
v___y_2732_ = v___y_2722_;
goto v___jp_2726_;
}
}
v___jp_2726_:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2716_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2733_, 1);
v___x_2734_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2716_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2781_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2781_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2781_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v_env_2740_; lean_object* v_nextMacroScope_2741_; lean_object* v_ngen_2742_; lean_object* v_auxDeclNGen_2743_; lean_object* v_traceState_2744_; lean_object* v_recordedDeps_2745_; lean_object* v_messages_2746_; lean_object* v_infoState_2747_; lean_object* v_snapshotTasks_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2779_; 
v___x_2739_ = lean_st_ref_take(v___y_2732_);
v_env_2740_ = lean_ctor_get(v___x_2739_, 0);
v_nextMacroScope_2741_ = lean_ctor_get(v___x_2739_, 1);
v_ngen_2742_ = lean_ctor_get(v___x_2739_, 2);
v_auxDeclNGen_2743_ = lean_ctor_get(v___x_2739_, 3);
v_traceState_2744_ = lean_ctor_get(v___x_2739_, 4);
v_recordedDeps_2745_ = lean_ctor_get(v___x_2739_, 6);
v_messages_2746_ = lean_ctor_get(v___x_2739_, 7);
v_infoState_2747_ = lean_ctor_get(v___x_2739_, 8);
v_snapshotTasks_2748_ = lean_ctor_get(v___x_2739_, 9);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v___x_2739_, 5);
lean_dec(v_unused_2780_);
v___x_2750_ = v___x_2739_;
v_isShared_2751_ = v_isSharedCheck_2779_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_snapshotTasks_2748_);
lean_inc(v_infoState_2747_);
lean_inc(v_messages_2746_);
lean_inc(v_recordedDeps_2745_);
lean_inc(v_traceState_2744_);
lean_inc(v_auxDeclNGen_2743_);
lean_inc(v_ngen_2742_);
lean_inc(v_nextMacroScope_2741_);
lean_inc(v_env_2740_);
lean_dec(v___x_2739_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2779_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2752_ = l_Lean_docStringExt;
v___x_2753_ = l_String_removeLeadingSpaces(v_a_2735_);
v___x_2754_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2752_, v_env_2740_, v_declName_2715_, v___x_2753_, v___x_2725_);
v___x_2755_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 5, v___x_2755_);
lean_ctor_set(v___x_2750_, 0, v___x_2754_);
v___x_2757_ = v___x_2750_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextMacroScope_2741_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_ngen_2742_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_auxDeclNGen_2743_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v_traceState_2744_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_recordedDeps_2745_);
lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_messages_2746_);
lean_ctor_set(v_reuseFailAlloc_2778_, 8, v_infoState_2747_);
lean_ctor_set(v_reuseFailAlloc_2778_, 9, v_snapshotTasks_2748_);
v___x_2757_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v_mctx_2760_; lean_object* v_zetaDeltaFVarIds_2761_; lean_object* v_postponed_2762_; lean_object* v_diag_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2776_; 
v___x_2758_ = lean_st_ref_put(v___y_2732_, v___x_2757_);
v___x_2759_ = lean_st_ref_take(v___y_2730_);
v_mctx_2760_ = lean_ctor_get(v___x_2759_, 0);
v_zetaDeltaFVarIds_2761_ = lean_ctor_get(v___x_2759_, 2);
v_postponed_2762_ = lean_ctor_get(v___x_2759_, 3);
v_diag_2763_ = lean_ctor_get(v___x_2759_, 4);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; 
v_unused_2777_ = lean_ctor_get(v___x_2759_, 1);
lean_dec(v_unused_2777_);
v___x_2765_ = v___x_2759_;
v_isShared_2766_ = v_isSharedCheck_2776_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_diag_2763_);
lean_inc(v_postponed_2762_);
lean_inc(v_zetaDeltaFVarIds_2761_);
lean_inc(v_mctx_2760_);
lean_dec(v___x_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2776_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2768_);
v___x_2770_ = v___x_2765_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_mctx_2760_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_zetaDeltaFVarIds_2761_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_postponed_2762_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_diag_2763_);
v___x_2770_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = lean_st_ref_put(v___y_2730_, v___x_2770_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2767_);
v___x_2773_ = v___x_2737_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2767_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_declName_2715_);
v_a_2782_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2734_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2734_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_dec(v_docComment_2716_);
lean_dec(v_declName_2715_);
return v___x_2733_;
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v_docComment_2716_);
lean_dec(v_declName_2715_);
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
LEAN_EXPORT void l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2715_ = stack[0].m_obj;
lean_object* v_docComment_2716_ = stack[1].m_obj;
lean_object* v___y_2717_ = stack[2].m_obj;
lean_object* v___y_2718_ = stack[3].m_obj;
lean_object* v___y_2719_ = stack[4].m_obj;
lean_object* v___y_2720_ = stack[5].m_obj;
lean_object* v___y_2721_ = stack[6].m_obj;
lean_object* v___y_2722_ = stack[7].m_obj;
lean_object* v_res_2801_;
v_res_2801_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2715_, v_docComment_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
stack->m_obj
 = v_res_2801_;
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2802_, lean_object* v_docComment_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2802_, v_docComment_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v_res_2811_;
}
}
lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2812_, lean_object* v_declName_2813_, lean_object* v_binders_2814_, lean_object* v_docComment_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
if (v_isVerso_2812_ == 0)
{
lean_object* v___x_2823_; 
lean_dec(v_binders_2814_);
v___x_2823_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2813_, v_docComment_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_addVersoDocString(v_declName_2813_, v_binders_2814_, v_docComment_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec(v_docComment_2815_);
return v___x_2824_;
}
}
}
LEAN_EXPORT void l_Lean_addDocStringOf_0interp(lean_interpreter_value* stack)
{
uint8_t v_isVerso_2812_ = stack[0].m_num;
lean_object* v_declName_2813_ = stack[1].m_obj;
lean_object* v_binders_2814_ = stack[2].m_obj;
lean_object* v_docComment_2815_ = stack[3].m_obj;
lean_object* v_a_2816_ = stack[4].m_obj;
lean_object* v_a_2817_ = stack[5].m_obj;
lean_object* v_a_2818_ = stack[6].m_obj;
lean_object* v_a_2819_ = stack[7].m_obj;
lean_object* v_a_2820_ = stack[8].m_obj;
lean_object* v_a_2821_ = stack[9].m_obj;
lean_object* v_res_2825_;
v_res_2825_ = l_Lean_addDocStringOf(v_isVerso_2812_, v_declName_2813_, v_binders_2814_, v_docComment_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
stack->m_obj
 = v_res_2825_;
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2826_, lean_object* v_declName_2827_, lean_object* v_binders_2828_, lean_object* v_docComment_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
uint8_t v_isVerso_boxed_2837_; lean_object* v_res_2838_; 
v_isVerso_boxed_2837_ = lean_unbox(v_isVerso_2826_);
v_res_2838_ = l_Lean_addDocStringOf(v_isVerso_boxed_2837_, v_declName_2827_, v_binders_2828_, v_docComment_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2838_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2839_, lean_object* v_msgData_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2839_, v_msgData_2840_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2839_ = stack[0].m_obj;
lean_object* v_msgData_2840_ = stack[1].m_obj;
lean_object* v___y_2841_ = stack[2].m_obj;
lean_object* v___y_2842_ = stack[3].m_obj;
lean_object* v___y_2843_ = stack[4].m_obj;
lean_object* v___y_2844_ = stack[5].m_obj;
lean_object* v___y_2845_ = stack[6].m_obj;
lean_object* v___y_2846_ = stack[7].m_obj;
lean_object* v_res_2849_;
v_res_2849_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2839_, v_msgData_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
stack->m_obj
 = v_res_2849_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2850_, lean_object* v_msgData_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2850_, v_msgData_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v_ref_2850_);
return v_res_2859_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2860_, lean_object* v_ref_2861_, lean_object* v_msg_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2861_, v_msg_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2861_ = stack[1].m_obj;
lean_object* v_msg_2862_ = stack[2].m_obj;
lean_object* v___y_2863_ = stack[3].m_obj;
lean_object* v___y_2864_ = stack[4].m_obj;
lean_object* v___y_2865_ = stack[5].m_obj;
lean_object* v___y_2866_ = stack[6].m_obj;
lean_object* v___y_2867_ = stack[7].m_obj;
lean_object* v___y_2868_ = stack[8].m_obj;
lean_object* v_res_2871_;
v_res_2871_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_box(0), v_ref_2861_, v_msg_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
stack->m_obj
 = v_res_2871_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_ref_2873_, lean_object* v_msg_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2872_, v_ref_2873_, v_msg_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v_ref_2873_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2883_, lean_object* v_t_2884_){
_start:
{
if (lean_obj_tag(v_t_2884_) == 0)
{
lean_object* v_k_2885_; lean_object* v_v_2886_; lean_object* v_l_2887_; lean_object* v_r_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_3542_; 
v_k_2885_ = lean_ctor_get(v_t_2884_, 1);
v_v_2886_ = lean_ctor_get(v_t_2884_, 2);
v_l_2887_ = lean_ctor_get(v_t_2884_, 3);
v_r_2888_ = lean_ctor_get(v_t_2884_, 4);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_t_2884_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v_t_2884_, 0);
lean_dec(v_unused_3543_);
v___x_2890_ = v_t_2884_;
v_isShared_2891_ = v_isSharedCheck_3542_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_r_2888_);
lean_inc(v_l_2887_);
lean_inc(v_v_2886_);
lean_inc(v_k_2885_);
lean_dec(v_t_2884_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_3542_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
uint8_t v___x_2892_; 
v___x_2892_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2883_, v_k_2885_);
switch(v___x_2892_)
{
case 0:
{
lean_object* v_impl_2893_; lean_object* v___x_2894_; 
v_impl_2893_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2883_, v_l_2887_);
v___x_2894_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2893_) == 0)
{
if (lean_obj_tag(v_r_2888_) == 0)
{
lean_object* v_size_2895_; lean_object* v_size_2896_; lean_object* v_k_2897_; lean_object* v_v_2898_; lean_object* v_l_2899_; lean_object* v_r_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v_size_2895_ = lean_ctor_get(v_impl_2893_, 0);
v_size_2896_ = lean_ctor_get(v_r_2888_, 0);
v_k_2897_ = lean_ctor_get(v_r_2888_, 1);
v_v_2898_ = lean_ctor_get(v_r_2888_, 2);
v_l_2899_ = lean_ctor_get(v_r_2888_, 3);
lean_inc(v_l_2899_);
v_r_2900_ = lean_ctor_get(v_r_2888_, 4);
v___x_2901_ = lean_unsigned_to_nat(3u);
v___x_2902_ = lean_nat_mul(v___x_2901_, v_size_2895_);
v___x_2903_ = lean_nat_dec_lt(v___x_2902_, v_size_2896_);
lean_dec(v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec(v_l_2899_);
v___x_2904_ = lean_nat_add(v___x_2894_, v_size_2895_);
v___x_2905_ = lean_nat_add(v___x_2904_, v_size_2896_);
lean_dec(v___x_2904_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 3, v_impl_2893_);
lean_ctor_set(v___x_2890_, 0, v___x_2905_);
v___x_2907_ = v___x_2890_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v_impl_2893_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v_r_2888_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
else
{
lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2972_; 
lean_inc(v_r_2900_);
lean_inc(v_v_2898_);
lean_inc(v_k_2897_);
lean_inc(v_size_2896_);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; lean_object* v_unused_2974_; lean_object* v_unused_2975_; lean_object* v_unused_2976_; lean_object* v_unused_2977_; 
v_unused_2973_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_2974_);
v_unused_2975_ = lean_ctor_get(v_r_2888_, 2);
lean_dec(v_unused_2975_);
v_unused_2976_ = lean_ctor_get(v_r_2888_, 1);
lean_dec(v_unused_2976_);
v_unused_2977_ = lean_ctor_get(v_r_2888_, 0);
lean_dec(v_unused_2977_);
v___x_2910_ = v_r_2888_;
v_isShared_2911_ = v_isSharedCheck_2972_;
goto v_resetjp_2909_;
}
else
{
lean_dec(v_r_2888_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2972_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v_size_2912_; lean_object* v_k_2913_; lean_object* v_v_2914_; lean_object* v_l_2915_; lean_object* v_r_2916_; lean_object* v_size_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_size_2912_ = lean_ctor_get(v_l_2899_, 0);
v_k_2913_ = lean_ctor_get(v_l_2899_, 1);
v_v_2914_ = lean_ctor_get(v_l_2899_, 2);
v_l_2915_ = lean_ctor_get(v_l_2899_, 3);
v_r_2916_ = lean_ctor_get(v_l_2899_, 4);
v_size_2917_ = lean_ctor_get(v_r_2900_, 0);
v___x_2918_ = lean_unsigned_to_nat(2u);
v___x_2919_ = lean_nat_mul(v___x_2918_, v_size_2917_);
v___x_2920_ = lean_nat_dec_lt(v_size_2912_, v___x_2919_);
lean_dec(v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2948_; 
lean_inc(v_r_2916_);
lean_inc(v_l_2915_);
lean_inc(v_v_2914_);
lean_inc(v_k_2913_);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_l_2899_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; lean_object* v_unused_2951_; lean_object* v_unused_2952_; lean_object* v_unused_2953_; 
v_unused_2949_ = lean_ctor_get(v_l_2899_, 4);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_l_2899_, 3);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_l_2899_, 2);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v_l_2899_, 1);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_l_2899_, 0);
lean_dec(v_unused_2953_);
v___x_2922_ = v_l_2899_;
v_isShared_2923_ = v_isSharedCheck_2948_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v_l_2899_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2948_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2938_; 
v___x_2924_ = lean_nat_add(v___x_2894_, v_size_2895_);
v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2896_);
lean_dec(v_size_2896_);
if (lean_obj_tag(v_l_2915_) == 0)
{
lean_object* v_size_2946_; 
v_size_2946_ = lean_ctor_get(v_l_2915_, 0);
lean_inc(v_size_2946_);
v___y_2938_ = v_size_2946_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_unsigned_to_nat(0u);
v___y_2938_ = v___x_2947_;
goto v___jp_2937_;
}
v___jp_2926_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_nat_add(v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec(v___y_2928_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 4, v_r_2900_);
lean_ctor_set(v___x_2922_, 3, v_r_2916_);
lean_ctor_set(v___x_2922_, 2, v_v_2898_);
lean_ctor_set(v___x_2922_, 1, v_k_2897_);
lean_ctor_set(v___x_2922_, 0, v___x_2930_);
v___x_2932_ = v___x_2922_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_k_2897_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_v_2898_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_r_2916_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_r_2900_);
v___x_2932_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2934_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 4, v___x_2932_);
lean_ctor_set(v___x_2910_, 3, v___y_2927_);
lean_ctor_set(v___x_2910_, 2, v_v_2914_);
lean_ctor_set(v___x_2910_, 1, v_k_2913_);
lean_ctor_set(v___x_2910_, 0, v___x_2925_);
v___x_2934_ = v___x_2910_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_k_2913_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_v_2914_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v___y_2927_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
v___jp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_nat_add(v___x_2924_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec(v___x_2924_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_l_2915_);
lean_ctor_set(v___x_2890_, 3, v_impl_2893_);
lean_ctor_set(v___x_2890_, 0, v___x_2939_);
v___x_2941_ = v___x_2890_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_impl_2893_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_l_2915_);
v___x_2941_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_nat_add(v___x_2894_, v_size_2917_);
if (lean_obj_tag(v_r_2916_) == 0)
{
lean_object* v_size_2943_; 
v_size_2943_ = lean_ctor_get(v_r_2916_, 0);
lean_inc(v_size_2943_);
v___y_2927_ = v___x_2941_;
v___y_2928_ = v___x_2942_;
v___y_2929_ = v_size_2943_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_unsigned_to_nat(0u);
v___y_2927_ = v___x_2941_;
v___y_2928_ = v___x_2942_;
v___y_2929_ = v___x_2944_;
goto v___jp_2926_;
}
}
}
}
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
lean_del_object(v___x_2890_);
v___x_2954_ = lean_nat_add(v___x_2894_, v_size_2895_);
v___x_2955_ = lean_nat_add(v___x_2954_, v_size_2896_);
lean_dec(v_size_2896_);
v___x_2956_ = lean_nat_add(v___x_2954_, v_size_2912_);
lean_dec(v___x_2954_);
lean_inc_ref(v_impl_2893_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 4, v_l_2899_);
lean_ctor_set(v___x_2910_, 3, v_impl_2893_);
lean_ctor_set(v___x_2910_, 2, v_v_2886_);
lean_ctor_set(v___x_2910_, 1, v_k_2885_);
lean_ctor_set(v___x_2910_, 0, v___x_2956_);
v___x_2958_ = v___x_2910_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_impl_2893_);
lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_l_2899_);
v___x_2958_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v_isSharedCheck_2965_ = !lean_is_exclusive(v_impl_2893_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; lean_object* v_unused_2968_; lean_object* v_unused_2969_; lean_object* v_unused_2970_; 
v_unused_2966_ = lean_ctor_get(v_impl_2893_, 4);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_impl_2893_, 3);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_impl_2893_, 2);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v_impl_2893_, 1);
lean_dec(v_unused_2969_);
v_unused_2970_ = lean_ctor_get(v_impl_2893_, 0);
lean_dec(v_unused_2970_);
v___x_2960_ = v_impl_2893_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_dec(v_impl_2893_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 4, v_r_2900_);
lean_ctor_set(v___x_2960_, 3, v___x_2958_);
lean_ctor_set(v___x_2960_, 2, v_v_2898_);
lean_ctor_set(v___x_2960_, 1, v_k_2897_);
lean_ctor_set(v___x_2960_, 0, v___x_2955_);
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2897_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2898_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_r_2900_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v_size_2978_ = lean_ctor_get(v_impl_2893_, 0);
v___x_2979_ = lean_nat_add(v___x_2894_, v_size_2978_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 3, v_impl_2893_);
lean_ctor_set(v___x_2890_, 0, v___x_2979_);
v___x_2981_ = v___x_2890_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_impl_2893_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_r_2888_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
else
{
if (lean_obj_tag(v_r_2888_) == 0)
{
lean_object* v_l_2983_; 
v_l_2983_ = lean_ctor_get(v_r_2888_, 3);
lean_inc(v_l_2983_);
if (lean_obj_tag(v_l_2983_) == 0)
{
lean_object* v_r_2984_; 
v_r_2984_ = lean_ctor_get(v_r_2888_, 4);
lean_inc(v_r_2984_);
if (lean_obj_tag(v_r_2984_) == 0)
{
lean_object* v_size_2985_; lean_object* v_k_2986_; lean_object* v_v_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3000_; 
v_size_2985_ = lean_ctor_get(v_r_2888_, 0);
v_k_2986_ = lean_ctor_get(v_r_2888_, 1);
v_v_2987_ = lean_ctor_get(v_r_2888_, 2);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; lean_object* v_unused_3002_; 
v_unused_3001_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3001_);
v_unused_3002_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3002_);
v___x_2989_ = v_r_2888_;
v_isShared_2990_ = v_isSharedCheck_3000_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_v_2987_);
lean_inc(v_k_2986_);
lean_inc(v_size_2985_);
lean_dec(v_r_2888_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3000_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_size_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v_size_2991_ = lean_ctor_get(v_l_2983_, 0);
v___x_2992_ = lean_nat_add(v___x_2894_, v_size_2985_);
lean_dec(v_size_2985_);
v___x_2993_ = lean_nat_add(v___x_2894_, v_size_2991_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 4, v_l_2983_);
lean_ctor_set(v___x_2989_, 3, v_impl_2893_);
lean_ctor_set(v___x_2989_, 2, v_v_2886_);
lean_ctor_set(v___x_2989_, 1, v_k_2885_);
lean_ctor_set(v___x_2989_, 0, v___x_2993_);
v___x_2995_ = v___x_2989_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_impl_2893_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_l_2983_);
v___x_2995_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_r_2984_);
lean_ctor_set(v___x_2890_, 3, v___x_2995_);
lean_ctor_set(v___x_2890_, 2, v_v_2987_);
lean_ctor_set(v___x_2890_, 1, v_k_2986_);
lean_ctor_set(v___x_2890_, 0, v___x_2992_);
v___x_2997_ = v___x_2890_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_k_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_v_2987_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_r_2984_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_k_3003_; lean_object* v_v_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3027_; 
v_k_3003_ = lean_ctor_get(v_r_2888_, 1);
v_v_3004_ = lean_ctor_get(v_r_2888_, 2);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; lean_object* v_unused_3029_; lean_object* v_unused_3030_; 
v_unused_3028_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3028_);
v_unused_3029_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3029_);
v_unused_3030_ = lean_ctor_get(v_r_2888_, 0);
lean_dec(v_unused_3030_);
v___x_3006_ = v_r_2888_;
v_isShared_3007_ = v_isSharedCheck_3027_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_v_3004_);
lean_inc(v_k_3003_);
lean_dec(v_r_2888_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3027_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v_k_3008_; lean_object* v_v_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3023_; 
v_k_3008_ = lean_ctor_get(v_l_2983_, 1);
v_v_3009_ = lean_ctor_get(v_l_2983_, 2);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_l_2983_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; lean_object* v_unused_3025_; lean_object* v_unused_3026_; 
v_unused_3024_ = lean_ctor_get(v_l_2983_, 4);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_l_2983_, 3);
lean_dec(v_unused_3025_);
v_unused_3026_ = lean_ctor_get(v_l_2983_, 0);
lean_dec(v_unused_3026_);
v___x_3011_ = v_l_2983_;
v_isShared_3012_ = v_isSharedCheck_3023_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_v_3009_);
lean_inc(v_k_3008_);
lean_dec(v_l_2983_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3023_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_unsigned_to_nat(3u);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v_r_2984_);
lean_ctor_set(v___x_3011_, 3, v_r_2984_);
lean_ctor_set(v___x_3011_, 2, v_v_2886_);
lean_ctor_set(v___x_3011_, 1, v_k_2885_);
lean_ctor_set(v___x_3011_, 0, v___x_2894_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_r_2984_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_r_2984_);
v___x_3015_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3017_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 3, v_r_2984_);
lean_ctor_set(v___x_3006_, 0, v___x_2894_);
v___x_3017_ = v___x_3006_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_k_3003_);
lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_v_3004_);
lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_r_2984_);
lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_r_2984_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_3017_);
lean_ctor_set(v___x_2890_, 3, v___x_3015_);
lean_ctor_set(v___x_2890_, 2, v_v_3009_);
lean_ctor_set(v___x_2890_, 1, v_k_3008_);
lean_ctor_set(v___x_2890_, 0, v___x_3013_);
v___x_3019_ = v___x_2890_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_k_3008_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_v_3009_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3020_, 4, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3031_; 
v_r_3031_ = lean_ctor_get(v_r_2888_, 4);
lean_inc(v_r_3031_);
if (lean_obj_tag(v_r_3031_) == 0)
{
lean_object* v_k_3032_; lean_object* v_v_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3044_; 
v_k_3032_ = lean_ctor_get(v_r_2888_, 1);
v_v_3033_ = lean_ctor_get(v_r_2888_, 2);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; lean_object* v_unused_3046_; lean_object* v_unused_3047_; 
v_unused_3045_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3045_);
v_unused_3046_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_r_2888_, 0);
lean_dec(v_unused_3047_);
v___x_3035_ = v_r_2888_;
v_isShared_3036_ = v_isSharedCheck_3044_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_v_3033_);
lean_inc(v_k_3032_);
lean_dec(v_r_2888_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3044_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = lean_unsigned_to_nat(3u);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 4, v_l_2983_);
lean_ctor_set(v___x_3035_, 2, v_v_2886_);
lean_ctor_set(v___x_3035_, 1, v_k_2885_);
lean_ctor_set(v___x_3035_, 0, v___x_2894_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3043_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3043_, 3, v_l_2983_);
lean_ctor_set(v_reuseFailAlloc_3043_, 4, v_l_2983_);
v___x_3039_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3041_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_r_3031_);
lean_ctor_set(v___x_2890_, 3, v___x_3039_);
lean_ctor_set(v___x_2890_, 2, v_v_3033_);
lean_ctor_set(v___x_2890_, 1, v_k_3032_);
lean_ctor_set(v___x_2890_, 0, v___x_3037_);
v___x_3041_ = v___x_2890_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_k_3032_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_v_3033_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_r_3031_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_size_3048_; lean_object* v_k_3049_; lean_object* v_v_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3061_; 
v_size_3048_ = lean_ctor_get(v_r_2888_, 0);
v_k_3049_ = lean_ctor_get(v_r_2888_, 1);
v_v_3050_ = lean_ctor_get(v_r_2888_, 2);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; lean_object* v_unused_3063_; 
v_unused_3062_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3062_);
v_unused_3063_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3063_);
v___x_3052_ = v_r_2888_;
v_isShared_3053_ = v_isSharedCheck_3061_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_v_3050_);
lean_inc(v_k_3049_);
lean_inc(v_size_3048_);
lean_dec(v_r_2888_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3061_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 3, v_r_3031_);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_size_3048_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_k_3049_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_v_3050_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_r_3031_);
lean_ctor_set(v_reuseFailAlloc_3060_, 4, v_r_3031_);
v___x_3055_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = lean_unsigned_to_nat(2u);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_3055_);
lean_ctor_set(v___x_2890_, 3, v_r_3031_);
lean_ctor_set(v___x_2890_, 0, v___x_3056_);
v___x_3058_ = v___x_2890_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v_r_3031_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v___x_3055_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
else
{
lean_object* v___x_3065_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 3, v_r_2888_);
lean_ctor_set(v___x_2890_, 0, v___x_2894_);
v___x_3065_ = v___x_2890_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3066_, 3, v_r_2888_);
lean_ctor_set(v_reuseFailAlloc_3066_, 4, v_r_2888_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2890_);
lean_dec(v_v_2886_);
lean_dec(v_k_2885_);
if (lean_obj_tag(v_l_2887_) == 0)
{
if (lean_obj_tag(v_r_2888_) == 0)
{
lean_object* v_size_3067_; lean_object* v_k_3068_; lean_object* v_v_3069_; lean_object* v_l_3070_; lean_object* v_r_3071_; lean_object* v_size_3072_; lean_object* v_k_3073_; lean_object* v_v_3074_; lean_object* v_l_3075_; lean_object* v_r_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v_size_3067_ = lean_ctor_get(v_l_2887_, 0);
v_k_3068_ = lean_ctor_get(v_l_2887_, 1);
v_v_3069_ = lean_ctor_get(v_l_2887_, 2);
v_l_3070_ = lean_ctor_get(v_l_2887_, 3);
v_r_3071_ = lean_ctor_get(v_l_2887_, 4);
lean_inc(v_r_3071_);
v_size_3072_ = lean_ctor_get(v_r_2888_, 0);
v_k_3073_ = lean_ctor_get(v_r_2888_, 1);
v_v_3074_ = lean_ctor_get(v_r_2888_, 2);
v_l_3075_ = lean_ctor_get(v_r_2888_, 3);
lean_inc(v_l_3075_);
v_r_3076_ = lean_ctor_get(v_r_2888_, 4);
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3078_ = lean_nat_dec_lt(v_size_3067_, v_size_3072_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3214_; 
lean_inc(v_l_3070_);
lean_inc(v_v_3069_);
lean_inc(v_k_3068_);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; lean_object* v_unused_3216_; lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3215_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_l_2887_, 2);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_l_2887_, 1);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3219_);
v___x_3080_ = v_l_2887_;
v_isShared_3081_ = v_isSharedCheck_3214_;
goto v_resetjp_3079_;
}
else
{
lean_dec(v_l_2887_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3214_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v_tree_3083_; 
v___x_3082_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3068_, v_v_3069_, v_l_3070_, v_r_3071_);
v_tree_3083_ = lean_ctor_get(v___x_3082_, 2);
if (lean_obj_tag(v_tree_3083_) == 0)
{
lean_object* v_k_3084_; lean_object* v_v_3085_; lean_object* v_size_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
lean_inc_ref(v_tree_3083_);
v_k_3084_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_k_3084_);
v_v_3085_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_v_3085_);
lean_dec_ref(v___x_3082_);
v_size_3086_ = lean_ctor_get(v_tree_3083_, 0);
v___x_3087_ = lean_unsigned_to_nat(3u);
v___x_3088_ = lean_nat_mul(v___x_3087_, v_size_3086_);
v___x_3089_ = lean_nat_dec_lt(v___x_3088_, v_size_3072_);
lean_dec(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
lean_dec(v_l_3075_);
v___x_3090_ = lean_nat_add(v___x_3077_, v_size_3086_);
v___x_3091_ = lean_nat_add(v___x_3090_, v_size_3072_);
lean_dec(v___x_3090_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v_r_2888_);
lean_ctor_set(v___x_3080_, 3, v_tree_3083_);
lean_ctor_set(v___x_3080_, 2, v_v_3085_);
lean_ctor_set(v___x_3080_, 1, v_k_3084_);
lean_ctor_set(v___x_3080_, 0, v___x_3091_);
v___x_3093_ = v___x_3080_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_k_3084_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_v_3085_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v_tree_3083_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_r_2888_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
else
{
lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3149_; 
lean_inc(v_r_3076_);
lean_inc(v_v_3074_);
lean_inc(v_k_3073_);
lean_inc(v_size_3072_);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; 
v_unused_3150_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_r_2888_, 2);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_r_2888_, 1);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_r_2888_, 0);
lean_dec(v_unused_3154_);
v___x_3096_ = v_r_2888_;
v_isShared_3097_ = v_isSharedCheck_3149_;
goto v_resetjp_3095_;
}
else
{
lean_dec(v_r_2888_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3149_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_size_3098_; lean_object* v_k_3099_; lean_object* v_v_3100_; lean_object* v_l_3101_; lean_object* v_r_3102_; lean_object* v_size_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_size_3098_ = lean_ctor_get(v_l_3075_, 0);
v_k_3099_ = lean_ctor_get(v_l_3075_, 1);
v_v_3100_ = lean_ctor_get(v_l_3075_, 2);
v_l_3101_ = lean_ctor_get(v_l_3075_, 3);
v_r_3102_ = lean_ctor_get(v_l_3075_, 4);
v_size_3103_ = lean_ctor_get(v_r_3076_, 0);
v___x_3104_ = lean_unsigned_to_nat(2u);
v___x_3105_ = lean_nat_mul(v___x_3104_, v_size_3103_);
v___x_3106_ = lean_nat_dec_lt(v_size_3098_, v___x_3105_);
lean_dec(v___x_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3134_; 
lean_inc(v_r_3102_);
lean_inc(v_l_3101_);
lean_inc(v_v_3100_);
lean_inc(v_k_3099_);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_l_3075_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; lean_object* v_unused_3138_; lean_object* v_unused_3139_; 
v_unused_3135_ = lean_ctor_get(v_l_3075_, 4);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_l_3075_, 3);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_l_3075_, 2);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_l_3075_, 1);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_l_3075_, 0);
lean_dec(v_unused_3139_);
v___x_3108_ = v_l_3075_;
v_isShared_3109_ = v_isSharedCheck_3134_;
goto v_resetjp_3107_;
}
else
{
lean_dec(v_l_3075_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3134_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3124_; 
v___x_3110_ = lean_nat_add(v___x_3077_, v_size_3086_);
v___x_3111_ = lean_nat_add(v___x_3110_, v_size_3072_);
lean_dec(v_size_3072_);
if (lean_obj_tag(v_l_3101_) == 0)
{
lean_object* v_size_3132_; 
v_size_3132_ = lean_ctor_get(v_l_3101_, 0);
lean_inc(v_size_3132_);
v___y_3124_ = v_size_3132_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_unsigned_to_nat(0u);
v___y_3124_ = v___x_3133_;
goto v___jp_3123_;
}
v___jp_3112_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_nat_add(v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec(v___y_3114_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 4, v_r_3076_);
lean_ctor_set(v___x_3108_, 3, v_r_3102_);
lean_ctor_set(v___x_3108_, 2, v_v_3074_);
lean_ctor_set(v___x_3108_, 1, v_k_3073_);
lean_ctor_set(v___x_3108_, 0, v___x_3116_);
v___x_3118_ = v___x_3108_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_r_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_r_3076_);
v___x_3118_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3120_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 4, v___x_3118_);
lean_ctor_set(v___x_3096_, 3, v___y_3113_);
lean_ctor_set(v___x_3096_, 2, v_v_3100_);
lean_ctor_set(v___x_3096_, 1, v_k_3099_);
lean_ctor_set(v___x_3096_, 0, v___x_3111_);
v___x_3120_ = v___x_3096_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_k_3099_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_v_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v___y_3113_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
v___jp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = lean_nat_add(v___x_3110_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec(v___x_3110_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v_l_3101_);
lean_ctor_set(v___x_3080_, 3, v_tree_3083_);
lean_ctor_set(v___x_3080_, 2, v_v_3085_);
lean_ctor_set(v___x_3080_, 1, v_k_3084_);
lean_ctor_set(v___x_3080_, 0, v___x_3125_);
v___x_3127_ = v___x_3080_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3084_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3085_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_tree_3083_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_l_3101_);
v___x_3127_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_nat_add(v___x_3077_, v_size_3103_);
if (lean_obj_tag(v_r_3102_) == 0)
{
lean_object* v_size_3129_; 
v_size_3129_ = lean_ctor_get(v_r_3102_, 0);
lean_inc(v_size_3129_);
v___y_3113_ = v___x_3127_;
v___y_3114_ = v___x_3128_;
v___y_3115_ = v_size_3129_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_unsigned_to_nat(0u);
v___y_3113_ = v___x_3127_;
v___y_3114_ = v___x_3128_;
v___y_3115_ = v___x_3130_;
goto v___jp_3112_;
}
}
}
}
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3140_ = lean_nat_add(v___x_3077_, v_size_3086_);
v___x_3141_ = lean_nat_add(v___x_3140_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3142_ = lean_nat_add(v___x_3140_, v_size_3098_);
lean_dec(v___x_3140_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 4, v_l_3075_);
lean_ctor_set(v___x_3096_, 3, v_tree_3083_);
lean_ctor_set(v___x_3096_, 2, v_v_3085_);
lean_ctor_set(v___x_3096_, 1, v_k_3084_);
lean_ctor_set(v___x_3096_, 0, v___x_3142_);
v___x_3144_ = v___x_3096_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_k_3084_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_v_3085_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_tree_3083_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_l_3075_);
v___x_3144_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3146_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v_r_3076_);
lean_ctor_set(v___x_3080_, 3, v___x_3144_);
lean_ctor_set(v___x_3080_, 2, v_v_3074_);
lean_ctor_set(v___x_3080_, 1, v_k_3073_);
lean_ctor_set(v___x_3080_, 0, v___x_3141_);
v___x_3146_ = v___x_3080_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_r_3076_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
else
{
lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3208_; 
lean_inc(v_r_3076_);
lean_inc(v_v_3074_);
lean_inc(v_k_3073_);
lean_inc(v_size_3072_);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; lean_object* v_unused_3210_; lean_object* v_unused_3211_; lean_object* v_unused_3212_; lean_object* v_unused_3213_; 
v_unused_3209_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3209_);
v_unused_3210_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3210_);
v_unused_3211_ = lean_ctor_get(v_r_2888_, 2);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v_r_2888_, 1);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_r_2888_, 0);
lean_dec(v_unused_3213_);
v___x_3156_ = v_r_2888_;
v_isShared_3157_ = v_isSharedCheck_3208_;
goto v_resetjp_3155_;
}
else
{
lean_dec(v_r_2888_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3208_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
if (lean_obj_tag(v_l_3075_) == 0)
{
if (lean_obj_tag(v_r_3076_) == 0)
{
lean_object* v_k_3158_; lean_object* v_v_3159_; lean_object* v_size_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_inc(v_tree_3083_);
v_k_3158_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_k_3158_);
v_v_3159_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_v_3159_);
lean_dec_ref(v___x_3082_);
v_size_3160_ = lean_ctor_get(v_l_3075_, 0);
v___x_3161_ = lean_nat_add(v___x_3077_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3162_ = lean_nat_add(v___x_3077_, v_size_3160_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 4, v_l_3075_);
lean_ctor_set(v___x_3156_, 3, v_tree_3083_);
lean_ctor_set(v___x_3156_, 2, v_v_3159_);
lean_ctor_set(v___x_3156_, 1, v_k_3158_);
lean_ctor_set(v___x_3156_, 0, v___x_3162_);
v___x_3164_ = v___x_3156_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_k_3158_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_v_3159_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_tree_3083_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v_l_3075_);
v___x_3164_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3166_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v_r_3076_);
lean_ctor_set(v___x_3080_, 3, v___x_3164_);
lean_ctor_set(v___x_3080_, 2, v_v_3074_);
lean_ctor_set(v___x_3080_, 1, v_k_3073_);
lean_ctor_set(v___x_3080_, 0, v___x_3161_);
v___x_3166_ = v___x_3080_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3167_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3167_, 3, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3167_, 4, v_r_3076_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
lean_object* v_k_3169_; lean_object* v_v_3170_; lean_object* v_k_3171_; lean_object* v_v_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_size_3072_);
v_k_3169_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_k_3169_);
v_v_3170_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_v_3170_);
lean_dec_ref(v___x_3082_);
v_k_3171_ = lean_ctor_get(v_l_3075_, 1);
v_v_3172_ = lean_ctor_get(v_l_3075_, 2);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_l_3075_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; 
v_unused_3187_ = lean_ctor_get(v_l_3075_, 4);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_l_3075_, 3);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_l_3075_, 0);
lean_dec(v_unused_3189_);
v___x_3174_ = v_l_3075_;
v_isShared_3175_ = v_isSharedCheck_3186_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_v_3172_);
lean_inc(v_k_3171_);
lean_dec(v_l_3075_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3186_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = lean_unsigned_to_nat(3u);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_r_3076_);
lean_ctor_set(v___x_3174_, 3, v_r_3076_);
lean_ctor_set(v___x_3174_, 2, v_v_3170_);
lean_ctor_set(v___x_3174_, 1, v_k_3169_);
lean_ctor_set(v___x_3174_, 0, v___x_3077_);
v___x_3178_ = v___x_3174_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v_r_3076_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_r_3076_);
v___x_3178_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3180_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 3, v_r_3076_);
lean_ctor_set(v___x_3156_, 0, v___x_3077_);
v___x_3180_ = v___x_3156_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_r_3076_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_r_3076_);
v___x_3180_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3182_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v___x_3180_);
lean_ctor_set(v___x_3080_, 3, v___x_3178_);
lean_ctor_set(v___x_3080_, 2, v_v_3172_);
lean_ctor_set(v___x_3080_, 1, v_k_3171_);
lean_ctor_set(v___x_3080_, 0, v___x_3176_);
v___x_3182_ = v___x_3080_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_k_3171_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_v_3172_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v___x_3178_);
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
}
else
{
if (lean_obj_tag(v_r_3076_) == 0)
{
lean_object* v_k_3190_; lean_object* v_v_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec(v_size_3072_);
v_k_3190_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_k_3190_);
v_v_3191_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_v_3191_);
lean_dec_ref(v___x_3082_);
v___x_3192_ = lean_unsigned_to_nat(3u);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 4, v_l_3075_);
lean_ctor_set(v___x_3156_, 2, v_v_3191_);
lean_ctor_set(v___x_3156_, 1, v_k_3190_);
lean_ctor_set(v___x_3156_, 0, v___x_3077_);
v___x_3194_ = v___x_3156_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_3190_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_3191_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_l_3075_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_l_3075_);
v___x_3194_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v_r_3076_);
lean_ctor_set(v___x_3080_, 3, v___x_3194_);
lean_ctor_set(v___x_3080_, 2, v_v_3074_);
lean_ctor_set(v___x_3080_, 1, v_k_3073_);
lean_ctor_set(v___x_3080_, 0, v___x_3192_);
v___x_3196_ = v___x_3080_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3197_, 4, v_r_3076_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
else
{
lean_object* v_k_3199_; lean_object* v_v_3200_; lean_object* v___x_3202_; 
v_k_3199_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_k_3199_);
v_v_3200_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_v_3200_);
lean_dec_ref(v___x_3082_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 3, v_r_3076_);
v___x_3202_ = v___x_3156_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_size_3072_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_r_3076_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_r_3076_);
v___x_3202_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_unsigned_to_nat(2u);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 4, v___x_3202_);
lean_ctor_set(v___x_3080_, 3, v_r_3076_);
lean_ctor_set(v___x_3080_, 2, v_v_3200_);
lean_ctor_set(v___x_3080_, 1, v_k_3199_);
lean_ctor_set(v___x_3080_, 0, v___x_3203_);
v___x_3205_ = v___x_3080_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_k_3199_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_v_3200_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_r_3076_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v___x_3202_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
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
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3372_; 
lean_inc(v_r_3076_);
lean_inc(v_v_3074_);
lean_inc(v_k_3073_);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_r_2888_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; lean_object* v_unused_3374_; lean_object* v_unused_3375_; lean_object* v_unused_3376_; lean_object* v_unused_3377_; 
v_unused_3373_ = lean_ctor_get(v_r_2888_, 4);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_r_2888_, 3);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v_r_2888_, 2);
lean_dec(v_unused_3375_);
v_unused_3376_ = lean_ctor_get(v_r_2888_, 1);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_r_2888_, 0);
lean_dec(v_unused_3377_);
v___x_3221_ = v_r_2888_;
v_isShared_3222_ = v_isSharedCheck_3372_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v_r_2888_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3372_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v_tree_3224_; 
v___x_3223_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3073_, v_v_3074_, v_l_3075_, v_r_3076_);
v_tree_3224_ = lean_ctor_get(v___x_3223_, 2);
lean_inc(v_tree_3224_);
if (lean_obj_tag(v_tree_3224_) == 0)
{
lean_object* v_k_3225_; lean_object* v_v_3226_; lean_object* v_size_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v_k_3225_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_k_3225_);
v_v_3226_ = lean_ctor_get(v___x_3223_, 1);
lean_inc(v_v_3226_);
lean_dec_ref(v___x_3223_);
v_size_3227_ = lean_ctor_get(v_tree_3224_, 0);
v___x_3228_ = lean_unsigned_to_nat(3u);
v___x_3229_ = lean_nat_mul(v___x_3228_, v_size_3227_);
v___x_3230_ = lean_nat_dec_lt(v___x_3229_, v_size_3067_);
lean_dec(v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
lean_dec(v_r_3071_);
v___x_3231_ = lean_nat_add(v___x_3077_, v_size_3067_);
v___x_3232_ = lean_nat_add(v___x_3231_, v_size_3227_);
lean_dec(v___x_3231_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_tree_3224_);
lean_ctor_set(v___x_3221_, 3, v_l_2887_);
lean_ctor_set(v___x_3221_, 2, v_v_3226_);
lean_ctor_set(v___x_3221_, 1, v_k_3225_);
lean_ctor_set(v___x_3221_, 0, v___x_3232_);
v___x_3234_ = v___x_3221_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_k_3225_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_v_3226_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v_tree_3224_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
else
{
lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3301_; 
lean_inc(v_l_3070_);
lean_inc(v_v_3069_);
lean_inc(v_k_3068_);
lean_inc(v_size_3067_);
v_isSharedCheck_3301_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3302_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_2887_, 2);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_2887_, 1);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3306_);
v___x_3237_ = v_l_2887_;
v_isShared_3238_ = v_isSharedCheck_3301_;
goto v_resetjp_3236_;
}
else
{
lean_dec(v_l_2887_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3301_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_size_3239_; lean_object* v_size_3240_; lean_object* v_k_3241_; lean_object* v_v_3242_; lean_object* v_l_3243_; lean_object* v_r_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_size_3239_ = lean_ctor_get(v_l_3070_, 0);
v_size_3240_ = lean_ctor_get(v_r_3071_, 0);
v_k_3241_ = lean_ctor_get(v_r_3071_, 1);
v_v_3242_ = lean_ctor_get(v_r_3071_, 2);
v_l_3243_ = lean_ctor_get(v_r_3071_, 3);
v_r_3244_ = lean_ctor_get(v_r_3071_, 4);
v___x_3245_ = lean_unsigned_to_nat(2u);
v___x_3246_ = lean_nat_mul(v___x_3245_, v_size_3239_);
v___x_3247_ = lean_nat_dec_lt(v_size_3240_, v___x_3246_);
lean_dec(v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3285_; 
lean_inc(v_r_3244_);
lean_inc(v_l_3243_);
lean_inc(v_v_3242_);
lean_inc(v_k_3241_);
lean_del_object(v___x_3237_);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_r_3071_);
if (v_isSharedCheck_3285_ == 0)
{
lean_object* v_unused_3286_; lean_object* v_unused_3287_; lean_object* v_unused_3288_; lean_object* v_unused_3289_; lean_object* v_unused_3290_; 
v_unused_3286_ = lean_ctor_get(v_r_3071_, 4);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_r_3071_, 3);
lean_dec(v_unused_3287_);
v_unused_3288_ = lean_ctor_get(v_r_3071_, 2);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_r_3071_, 1);
lean_dec(v_unused_3289_);
v_unused_3290_ = lean_ctor_get(v_r_3071_, 0);
lean_dec(v_unused_3290_);
v___x_3249_ = v_r_3071_;
v_isShared_3250_ = v_isSharedCheck_3285_;
goto v_resetjp_3248_;
}
else
{
lean_dec(v_r_3071_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3285_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___x_3273_; lean_object* v___y_3275_; 
v___x_3251_ = lean_nat_add(v___x_3077_, v_size_3067_);
lean_dec(v_size_3067_);
v___x_3252_ = lean_nat_add(v___x_3251_, v_size_3227_);
lean_dec(v___x_3251_);
v___x_3273_ = lean_nat_add(v___x_3077_, v_size_3239_);
if (lean_obj_tag(v_l_3243_) == 0)
{
lean_object* v_size_3283_; 
v_size_3283_ = lean_ctor_get(v_l_3243_, 0);
lean_inc(v_size_3283_);
v___y_3275_ = v_size_3283_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_unsigned_to_nat(0u);
v___y_3275_ = v___x_3284_;
goto v___jp_3274_;
}
v___jp_3253_:
{
lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3257_ = lean_nat_add(v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_inc_ref(v_tree_3224_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 4, v_tree_3224_);
lean_ctor_set(v___x_3249_, 3, v_r_3244_);
lean_ctor_set(v___x_3249_, 2, v_v_3226_);
lean_ctor_set(v___x_3249_, 1, v_k_3225_);
lean_ctor_set(v___x_3249_, 0, v___x_3257_);
v___x_3259_ = v___x_3249_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_k_3225_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_v_3226_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_r_3244_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_tree_3224_);
v___x_3259_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
v_isSharedCheck_3266_ = !lean_is_exclusive(v_tree_3224_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; lean_object* v_unused_3268_; lean_object* v_unused_3269_; lean_object* v_unused_3270_; lean_object* v_unused_3271_; 
v_unused_3267_ = lean_ctor_get(v_tree_3224_, 4);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_tree_3224_, 3);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_tree_3224_, 2);
lean_dec(v_unused_3269_);
v_unused_3270_ = lean_ctor_get(v_tree_3224_, 1);
lean_dec(v_unused_3270_);
v_unused_3271_ = lean_ctor_get(v_tree_3224_, 0);
lean_dec(v_unused_3271_);
v___x_3261_ = v_tree_3224_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_dec(v_tree_3224_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 4, v___x_3259_);
lean_ctor_set(v___x_3261_, 3, v___y_3254_);
lean_ctor_set(v___x_3261_, 2, v_v_3242_);
lean_ctor_set(v___x_3261_, 1, v_k_3241_);
lean_ctor_set(v___x_3261_, 0, v___x_3252_);
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_k_3241_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_v_3242_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v___y_3254_);
lean_ctor_set(v_reuseFailAlloc_3265_, 4, v___x_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
v___jp_3274_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = lean_nat_add(v___x_3273_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec(v___x_3273_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_l_3243_);
lean_ctor_set(v___x_3221_, 3, v_l_3070_);
lean_ctor_set(v___x_3221_, 2, v_v_3069_);
lean_ctor_set(v___x_3221_, 1, v_k_3068_);
lean_ctor_set(v___x_3221_, 0, v___x_3276_);
v___x_3278_ = v___x_3221_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_k_3068_);
lean_ctor_set(v_reuseFailAlloc_3282_, 2, v_v_3069_);
lean_ctor_set(v_reuseFailAlloc_3282_, 3, v_l_3070_);
lean_ctor_set(v_reuseFailAlloc_3282_, 4, v_l_3243_);
v___x_3278_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_nat_add(v___x_3077_, v_size_3227_);
if (lean_obj_tag(v_r_3244_) == 0)
{
lean_object* v_size_3280_; 
v_size_3280_ = lean_ctor_get(v_r_3244_, 0);
lean_inc(v_size_3280_);
v___y_3254_ = v___x_3278_;
v___y_3255_ = v___x_3279_;
v___y_3256_ = v_size_3280_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_unsigned_to_nat(0u);
v___y_3254_ = v___x_3278_;
v___y_3255_ = v___x_3279_;
v___y_3256_ = v___x_3281_;
goto v___jp_3253_;
}
}
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3291_ = lean_nat_add(v___x_3077_, v_size_3067_);
lean_dec(v_size_3067_);
v___x_3292_ = lean_nat_add(v___x_3291_, v_size_3227_);
lean_dec(v___x_3291_);
v___x_3293_ = lean_nat_add(v___x_3077_, v_size_3227_);
v___x_3294_ = lean_nat_add(v___x_3293_, v_size_3240_);
lean_dec(v___x_3293_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_tree_3224_);
lean_ctor_set(v___x_3221_, 3, v_r_3071_);
lean_ctor_set(v___x_3221_, 2, v_v_3226_);
lean_ctor_set(v___x_3221_, 1, v_k_3225_);
lean_ctor_set(v___x_3221_, 0, v___x_3294_);
v___x_3296_ = v___x_3221_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3225_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3226_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v_r_3071_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_tree_3224_);
v___x_3296_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 4, v___x_3296_);
lean_ctor_set(v___x_3237_, 0, v___x_3292_);
v___x_3298_ = v___x_3237_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v_k_3068_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v_v_3069_);
lean_ctor_set(v_reuseFailAlloc_3299_, 3, v_l_3070_);
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
if (lean_obj_tag(v_l_3070_) == 0)
{
lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3330_; 
lean_inc_ref(v_l_3070_);
lean_inc(v_v_3069_);
lean_inc(v_k_3068_);
lean_inc(v_size_3067_);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; lean_object* v_unused_3332_; lean_object* v_unused_3333_; lean_object* v_unused_3334_; lean_object* v_unused_3335_; 
v_unused_3331_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3331_);
v_unused_3332_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3332_);
v_unused_3333_ = lean_ctor_get(v_l_2887_, 2);
lean_dec(v_unused_3333_);
v_unused_3334_ = lean_ctor_get(v_l_2887_, 1);
lean_dec(v_unused_3334_);
v_unused_3335_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3335_);
v___x_3308_ = v_l_2887_;
v_isShared_3309_ = v_isSharedCheck_3330_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v_l_2887_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3330_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
if (lean_obj_tag(v_r_3071_) == 0)
{
lean_object* v_k_3310_; lean_object* v_v_3311_; lean_object* v_size_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v_k_3310_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_k_3310_);
v_v_3311_ = lean_ctor_get(v___x_3223_, 1);
lean_inc(v_v_3311_);
lean_dec_ref(v___x_3223_);
v_size_3312_ = lean_ctor_get(v_r_3071_, 0);
v___x_3313_ = lean_nat_add(v___x_3077_, v_size_3067_);
lean_dec(v_size_3067_);
v___x_3314_ = lean_nat_add(v___x_3077_, v_size_3312_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_tree_3224_);
lean_ctor_set(v___x_3221_, 3, v_r_3071_);
lean_ctor_set(v___x_3221_, 2, v_v_3311_);
lean_ctor_set(v___x_3221_, 1, v_k_3310_);
lean_ctor_set(v___x_3221_, 0, v___x_3314_);
v___x_3316_ = v___x_3221_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_k_3310_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_v_3311_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v_r_3071_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v_tree_3224_);
v___x_3316_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v___x_3316_);
lean_ctor_set(v___x_3308_, 0, v___x_3313_);
v___x_3318_ = v___x_3308_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_k_3068_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_v_3069_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v_l_3070_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
else
{
lean_object* v_k_3321_; lean_object* v_v_3322_; lean_object* v___x_3323_; lean_object* v___x_3325_; 
lean_dec(v_size_3067_);
v_k_3321_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_k_3321_);
v_v_3322_ = lean_ctor_get(v___x_3223_, 1);
lean_inc(v_v_3322_);
lean_dec_ref(v___x_3223_);
v___x_3323_ = lean_unsigned_to_nat(3u);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_r_3071_);
lean_ctor_set(v___x_3221_, 3, v_r_3071_);
lean_ctor_set(v___x_3221_, 2, v_v_3322_);
lean_ctor_set(v___x_3221_, 1, v_k_3321_);
lean_ctor_set(v___x_3221_, 0, v___x_3077_);
v___x_3325_ = v___x_3221_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_k_3321_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_v_3322_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_r_3071_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_r_3071_);
v___x_3325_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3327_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v___x_3325_);
lean_ctor_set(v___x_3308_, 0, v___x_3323_);
v___x_3327_ = v___x_3308_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_k_3068_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v_v_3069_);
lean_ctor_set(v_reuseFailAlloc_3328_, 3, v_l_3070_);
lean_ctor_set(v_reuseFailAlloc_3328_, 4, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3071_) == 0)
{
lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3360_; 
lean_inc(v_l_3070_);
lean_inc(v_v_3069_);
lean_inc(v_k_3068_);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; lean_object* v_unused_3362_; lean_object* v_unused_3363_; lean_object* v_unused_3364_; lean_object* v_unused_3365_; 
v_unused_3361_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3361_);
v_unused_3362_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3362_);
v_unused_3363_ = lean_ctor_get(v_l_2887_, 2);
lean_dec(v_unused_3363_);
v_unused_3364_ = lean_ctor_get(v_l_2887_, 1);
lean_dec(v_unused_3364_);
v_unused_3365_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3365_);
v___x_3337_ = v_l_2887_;
v_isShared_3338_ = v_isSharedCheck_3360_;
goto v_resetjp_3336_;
}
else
{
lean_dec(v_l_2887_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3360_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_k_3339_; lean_object* v_v_3340_; lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3356_; 
v_k_3339_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_k_3339_);
v_v_3340_ = lean_ctor_get(v___x_3223_, 1);
lean_inc(v_v_3340_);
lean_dec_ref(v___x_3223_);
v_k_3341_ = lean_ctor_get(v_r_3071_, 1);
v_v_3342_ = lean_ctor_get(v_r_3071_, 2);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_r_3071_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; lean_object* v_unused_3358_; lean_object* v_unused_3359_; 
v_unused_3357_ = lean_ctor_get(v_r_3071_, 4);
lean_dec(v_unused_3357_);
v_unused_3358_ = lean_ctor_get(v_r_3071_, 3);
lean_dec(v_unused_3358_);
v_unused_3359_ = lean_ctor_get(v_r_3071_, 0);
lean_dec(v_unused_3359_);
v___x_3344_ = v_r_3071_;
v_isShared_3345_ = v_isSharedCheck_3356_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
lean_dec(v_r_3071_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3356_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_unsigned_to_nat(3u);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 4, v_l_3070_);
lean_ctor_set(v___x_3344_, 3, v_l_3070_);
lean_ctor_set(v___x_3344_, 2, v_v_3069_);
lean_ctor_set(v___x_3344_, 1, v_k_3068_);
lean_ctor_set(v___x_3344_, 0, v___x_3077_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_k_3068_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_v_3069_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_l_3070_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_l_3070_);
v___x_3348_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_l_3070_);
lean_ctor_set(v___x_3221_, 3, v_l_3070_);
lean_ctor_set(v___x_3221_, 2, v_v_3340_);
lean_ctor_set(v___x_3221_, 1, v_k_3339_);
lean_ctor_set(v___x_3221_, 0, v___x_3077_);
v___x_3350_ = v___x_3221_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_k_3339_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_v_3340_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v_l_3070_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v_l_3070_);
v___x_3350_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3352_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 4, v___x_3350_);
lean_ctor_set(v___x_3337_, 3, v___x_3348_);
lean_ctor_set(v___x_3337_, 2, v_v_3342_);
lean_ctor_set(v___x_3337_, 1, v_k_3341_);
lean_ctor_set(v___x_3337_, 0, v___x_3346_);
v___x_3352_ = v___x_3337_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
else
{
lean_object* v_k_3366_; lean_object* v_v_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v_k_3366_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_k_3366_);
v_v_3367_ = lean_ctor_get(v___x_3223_, 1);
lean_inc(v_v_3367_);
lean_dec_ref(v___x_3223_);
v___x_3368_ = lean_unsigned_to_nat(2u);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_r_3071_);
lean_ctor_set(v___x_3221_, 3, v_l_2887_);
lean_ctor_set(v___x_3221_, 2, v_v_3367_);
lean_ctor_set(v___x_3221_, 1, v_k_3366_);
lean_ctor_set(v___x_3221_, 0, v___x_3368_);
v___x_3370_ = v___x_3221_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_k_3366_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_v_3367_);
lean_ctor_set(v_reuseFailAlloc_3371_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_3371_, 4, v_r_3071_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
}
}
else
{
return v_l_2887_;
}
}
else
{
return v_r_2888_;
}
}
default: 
{
lean_object* v_impl_3378_; lean_object* v___x_3379_; 
v_impl_3378_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2883_, v_r_2888_);
v___x_3379_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3378_) == 0)
{
if (lean_obj_tag(v_l_2887_) == 0)
{
lean_object* v_size_3380_; lean_object* v_size_3381_; lean_object* v_k_3382_; lean_object* v_v_3383_; lean_object* v_l_3384_; lean_object* v_r_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v_size_3380_ = lean_ctor_get(v_impl_3378_, 0);
v_size_3381_ = lean_ctor_get(v_l_2887_, 0);
v_k_3382_ = lean_ctor_get(v_l_2887_, 1);
v_v_3383_ = lean_ctor_get(v_l_2887_, 2);
v_l_3384_ = lean_ctor_get(v_l_2887_, 3);
v_r_3385_ = lean_ctor_get(v_l_2887_, 4);
lean_inc(v_r_3385_);
v___x_3386_ = lean_unsigned_to_nat(3u);
v___x_3387_ = lean_nat_mul(v___x_3386_, v_size_3380_);
v___x_3388_ = lean_nat_dec_lt(v___x_3387_, v_size_3381_);
lean_dec(v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
lean_dec(v_r_3385_);
v___x_3389_ = lean_nat_add(v___x_3379_, v_size_3381_);
v___x_3390_ = lean_nat_add(v___x_3389_, v_size_3380_);
lean_dec(v___x_3389_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_impl_3378_);
lean_ctor_set(v___x_2890_, 0, v___x_3390_);
v___x_3392_ = v___x_2890_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_impl_3378_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
else
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3459_; 
lean_inc(v_l_3384_);
lean_inc(v_v_3383_);
lean_inc(v_k_3382_);
lean_inc(v_size_3381_);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; lean_object* v_unused_3461_; lean_object* v_unused_3462_; lean_object* v_unused_3463_; lean_object* v_unused_3464_; 
v_unused_3460_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3460_);
v_unused_3461_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_l_2887_, 2);
lean_dec(v_unused_3462_);
v_unused_3463_ = lean_ctor_get(v_l_2887_, 1);
lean_dec(v_unused_3463_);
v_unused_3464_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3464_);
v___x_3395_ = v_l_2887_;
v_isShared_3396_ = v_isSharedCheck_3459_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v_l_2887_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3459_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_size_3397_; lean_object* v_size_3398_; lean_object* v_k_3399_; lean_object* v_v_3400_; lean_object* v_l_3401_; lean_object* v_r_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v_size_3397_ = lean_ctor_get(v_l_3384_, 0);
v_size_3398_ = lean_ctor_get(v_r_3385_, 0);
v_k_3399_ = lean_ctor_get(v_r_3385_, 1);
v_v_3400_ = lean_ctor_get(v_r_3385_, 2);
v_l_3401_ = lean_ctor_get(v_r_3385_, 3);
v_r_3402_ = lean_ctor_get(v_r_3385_, 4);
v___x_3403_ = lean_unsigned_to_nat(2u);
v___x_3404_ = lean_nat_mul(v___x_3403_, v_size_3397_);
v___x_3405_ = lean_nat_dec_lt(v_size_3398_, v___x_3404_);
lean_dec(v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3434_; 
lean_inc(v_r_3402_);
lean_inc(v_l_3401_);
lean_inc(v_v_3400_);
lean_inc(v_k_3399_);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_r_3385_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; lean_object* v_unused_3436_; lean_object* v_unused_3437_; lean_object* v_unused_3438_; lean_object* v_unused_3439_; 
v_unused_3435_ = lean_ctor_get(v_r_3385_, 4);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v_r_3385_, 3);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_r_3385_, 2);
lean_dec(v_unused_3437_);
v_unused_3438_ = lean_ctor_get(v_r_3385_, 1);
lean_dec(v_unused_3438_);
v_unused_3439_ = lean_ctor_get(v_r_3385_, 0);
lean_dec(v_unused_3439_);
v___x_3407_ = v_r_3385_;
v_isShared_3408_ = v_isSharedCheck_3434_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v_r_3385_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3434_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___x_3422_; lean_object* v___y_3424_; 
v___x_3409_ = lean_nat_add(v___x_3379_, v_size_3381_);
lean_dec(v_size_3381_);
v___x_3410_ = lean_nat_add(v___x_3409_, v_size_3380_);
lean_dec(v___x_3409_);
v___x_3422_ = lean_nat_add(v___x_3379_, v_size_3397_);
if (lean_obj_tag(v_l_3401_) == 0)
{
lean_object* v_size_3432_; 
v_size_3432_ = lean_ctor_get(v_l_3401_, 0);
lean_inc(v_size_3432_);
v___y_3424_ = v_size_3432_;
goto v___jp_3423_;
}
else
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_unsigned_to_nat(0u);
v___y_3424_ = v___x_3433_;
goto v___jp_3423_;
}
v___jp_3411_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_nat_add(v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec(v___y_3413_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_impl_3378_);
lean_ctor_set(v___x_3407_, 3, v_r_3402_);
lean_ctor_set(v___x_3407_, 2, v_v_2886_);
lean_ctor_set(v___x_3407_, 1, v_k_2885_);
lean_ctor_set(v___x_3407_, 0, v___x_3415_);
v___x_3417_ = v___x_3407_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3421_, 3, v_r_3402_);
lean_ctor_set(v_reuseFailAlloc_3421_, 4, v_impl_3378_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 4, v___x_3417_);
lean_ctor_set(v___x_3395_, 3, v___y_3412_);
lean_ctor_set(v___x_3395_, 2, v_v_3400_);
lean_ctor_set(v___x_3395_, 1, v_k_3399_);
lean_ctor_set(v___x_3395_, 0, v___x_3410_);
v___x_3419_ = v___x_3395_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_k_3399_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_v_3400_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v___y_3412_);
lean_ctor_set(v_reuseFailAlloc_3420_, 4, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
v___jp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3425_ = lean_nat_add(v___x_3422_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec(v___x_3422_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_l_3401_);
lean_ctor_set(v___x_2890_, 3, v_l_3384_);
lean_ctor_set(v___x_2890_, 2, v_v_3383_);
lean_ctor_set(v___x_2890_, 1, v_k_3382_);
lean_ctor_set(v___x_2890_, 0, v___x_3425_);
v___x_3427_ = v___x_2890_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_k_3382_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_v_3383_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_l_3384_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_l_3401_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_nat_add(v___x_3379_, v_size_3380_);
if (lean_obj_tag(v_r_3402_) == 0)
{
lean_object* v_size_3429_; 
v_size_3429_ = lean_ctor_get(v_r_3402_, 0);
lean_inc(v_size_3429_);
v___y_3412_ = v___x_3427_;
v___y_3413_ = v___x_3428_;
v___y_3414_ = v_size_3429_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_unsigned_to_nat(0u);
v___y_3412_ = v___x_3427_;
v___y_3413_ = v___x_3428_;
v___y_3414_ = v___x_3430_;
goto v___jp_3411_;
}
}
}
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
lean_del_object(v___x_2890_);
v___x_3440_ = lean_nat_add(v___x_3379_, v_size_3381_);
lean_dec(v_size_3381_);
v___x_3441_ = lean_nat_add(v___x_3440_, v_size_3380_);
lean_dec(v___x_3440_);
v___x_3442_ = lean_nat_add(v___x_3379_, v_size_3380_);
v___x_3443_ = lean_nat_add(v___x_3442_, v_size_3398_);
lean_dec(v___x_3442_);
lean_inc_ref(v_impl_3378_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 4, v_impl_3378_);
lean_ctor_set(v___x_3395_, 3, v_r_3385_);
lean_ctor_set(v___x_3395_, 2, v_v_2886_);
lean_ctor_set(v___x_3395_, 1, v_k_2885_);
lean_ctor_set(v___x_3395_, 0, v___x_3443_);
v___x_3445_ = v___x_3395_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_r_3385_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_impl_3378_);
v___x_3445_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v_isSharedCheck_3452_ = !lean_is_exclusive(v_impl_3378_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; lean_object* v_unused_3454_; lean_object* v_unused_3455_; lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3453_ = lean_ctor_get(v_impl_3378_, 4);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v_impl_3378_, 3);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_impl_3378_, 2);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_impl_3378_, 1);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_impl_3378_, 0);
lean_dec(v_unused_3457_);
v___x_3447_ = v_impl_3378_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_dec(v_impl_3378_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 4, v___x_3445_);
lean_ctor_set(v___x_3447_, 3, v_l_3384_);
lean_ctor_set(v___x_3447_, 2, v_v_3383_);
lean_ctor_set(v___x_3447_, 1, v_k_3382_);
lean_ctor_set(v___x_3447_, 0, v___x_3441_);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3382_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3383_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_l_3384_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v___x_3445_);
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
}
}
}
else
{
lean_object* v_size_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v_size_3465_ = lean_ctor_get(v_impl_3378_, 0);
v___x_3466_ = lean_nat_add(v___x_3379_, v_size_3465_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_impl_3378_);
lean_ctor_set(v___x_2890_, 0, v___x_3466_);
v___x_3468_ = v___x_2890_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_impl_3378_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
else
{
if (lean_obj_tag(v_l_2887_) == 0)
{
lean_object* v_l_3470_; 
v_l_3470_ = lean_ctor_get(v_l_2887_, 3);
if (lean_obj_tag(v_l_3470_) == 0)
{
lean_object* v_r_3471_; 
lean_inc_ref(v_l_3470_);
v_r_3471_ = lean_ctor_get(v_l_2887_, 4);
lean_inc(v_r_3471_);
if (lean_obj_tag(v_r_3471_) == 0)
{
lean_object* v_size_3472_; lean_object* v_k_3473_; lean_object* v_v_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3487_; 
v_size_3472_ = lean_ctor_get(v_l_2887_, 0);
v_k_3473_ = lean_ctor_get(v_l_2887_, 1);
v_v_3474_ = lean_ctor_get(v_l_2887_, 2);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3488_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3489_);
v___x_3476_ = v_l_2887_;
v_isShared_3477_ = v_isSharedCheck_3487_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_v_3474_);
lean_inc(v_k_3473_);
lean_inc(v_size_3472_);
lean_dec(v_l_2887_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3487_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_size_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v_size_3478_ = lean_ctor_get(v_r_3471_, 0);
v___x_3479_ = lean_nat_add(v___x_3379_, v_size_3472_);
lean_dec(v_size_3472_);
v___x_3480_ = lean_nat_add(v___x_3379_, v_size_3478_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_impl_3378_);
lean_ctor_set(v___x_3476_, 3, v_r_3471_);
lean_ctor_set(v___x_3476_, 2, v_v_2886_);
lean_ctor_set(v___x_3476_, 1, v_k_2885_);
lean_ctor_set(v___x_3476_, 0, v___x_3480_);
v___x_3482_ = v___x_3476_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_r_3471_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_impl_3378_);
v___x_3482_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_3482_);
lean_ctor_set(v___x_2890_, 3, v_l_3470_);
lean_ctor_set(v___x_2890_, 2, v_v_3474_);
lean_ctor_set(v___x_2890_, 1, v_k_3473_);
lean_ctor_set(v___x_2890_, 0, v___x_3479_);
v___x_3484_ = v___x_2890_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_3473_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_3474_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_l_3470_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v___x_3482_);
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
lean_object* v_k_3490_; lean_object* v_v_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3502_; 
v_k_3490_ = lean_ctor_get(v_l_2887_, 1);
v_v_3491_ = lean_ctor_get(v_l_2887_, 2);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; lean_object* v_unused_3504_; lean_object* v_unused_3505_; 
v_unused_3503_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3505_);
v___x_3493_ = v_l_2887_;
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_v_3491_);
lean_inc(v_k_3490_);
lean_dec(v_l_2887_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_unsigned_to_nat(3u);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 3, v_r_3471_);
lean_ctor_set(v___x_3493_, 2, v_v_2886_);
lean_ctor_set(v___x_3493_, 1, v_k_2885_);
lean_ctor_set(v___x_3493_, 0, v___x_3379_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_r_3471_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_r_3471_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_3497_);
lean_ctor_set(v___x_2890_, 3, v_l_3470_);
lean_ctor_set(v___x_2890_, 2, v_v_3491_);
lean_ctor_set(v___x_2890_, 1, v_k_3490_);
lean_ctor_set(v___x_2890_, 0, v___x_3495_);
v___x_3499_ = v___x_2890_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_l_3470_);
lean_ctor_set(v_reuseFailAlloc_3500_, 4, v___x_3497_);
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
else
{
lean_object* v_r_3506_; 
v_r_3506_ = lean_ctor_get(v_l_2887_, 4);
lean_inc(v_r_3506_);
if (lean_obj_tag(v_r_3506_) == 0)
{
lean_object* v_k_3507_; lean_object* v_v_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3531_; 
lean_inc(v_l_3470_);
v_k_3507_ = lean_ctor_get(v_l_2887_, 1);
v_v_3508_ = lean_ctor_get(v_l_2887_, 2);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_l_2887_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; lean_object* v_unused_3533_; lean_object* v_unused_3534_; 
v_unused_3532_ = lean_ctor_get(v_l_2887_, 4);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_l_2887_, 3);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_l_2887_, 0);
lean_dec(v_unused_3534_);
v___x_3510_ = v_l_2887_;
v_isShared_3511_ = v_isSharedCheck_3531_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_v_3508_);
lean_inc(v_k_3507_);
lean_dec(v_l_2887_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3531_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_k_3512_; lean_object* v_v_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3527_; 
v_k_3512_ = lean_ctor_get(v_r_3506_, 1);
v_v_3513_ = lean_ctor_get(v_r_3506_, 2);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_r_3506_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; lean_object* v_unused_3529_; lean_object* v_unused_3530_; 
v_unused_3528_ = lean_ctor_get(v_r_3506_, 4);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_r_3506_, 3);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v_r_3506_, 0);
lean_dec(v_unused_3530_);
v___x_3515_ = v_r_3506_;
v_isShared_3516_ = v_isSharedCheck_3527_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_v_3513_);
lean_inc(v_k_3512_);
lean_dec(v_r_3506_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3527_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = lean_unsigned_to_nat(3u);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 4, v_l_3470_);
lean_ctor_set(v___x_3515_, 3, v_l_3470_);
lean_ctor_set(v___x_3515_, 2, v_v_3508_);
lean_ctor_set(v___x_3515_, 1, v_k_3507_);
lean_ctor_set(v___x_3515_, 0, v___x_3379_);
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_k_3507_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_v_3508_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_l_3470_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_l_3470_);
v___x_3519_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 4, v_l_3470_);
lean_ctor_set(v___x_3510_, 2, v_v_2886_);
lean_ctor_set(v___x_3510_, 1, v_k_2885_);
lean_ctor_set(v___x_3510_, 0, v___x_3379_);
v___x_3521_ = v___x_3510_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_l_3470_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_l_3470_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_3521_);
lean_ctor_set(v___x_2890_, 3, v___x_3519_);
lean_ctor_set(v___x_2890_, 2, v_v_3513_);
lean_ctor_set(v___x_2890_, 1, v_k_3512_);
lean_ctor_set(v___x_2890_, 0, v___x_3517_);
v___x_3523_ = v___x_2890_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_k_3512_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_v_3513_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_unsigned_to_nat(2u);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_r_3506_);
lean_ctor_set(v___x_2890_, 0, v___x_3535_);
v___x_3537_ = v___x_2890_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v_r_3506_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v___x_3540_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_l_2887_);
lean_ctor_set(v___x_2890_, 0, v___x_3379_);
v___x_3540_ = v___x_2890_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_3541_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_3541_, 4, v_l_2887_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
}
}
else
{
return v_t_2884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3544_, lean_object* v_t_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3544_, v_t_3545_);
lean_dec(v_k_3544_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3547_, lean_object* v_ps_3548_){
_start:
{
lean_object* v_importedEntries_3549_; lean_object* v_state_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3558_; 
v_importedEntries_3549_ = lean_ctor_get(v_ps_3548_, 0);
v_state_3550_ = lean_ctor_get(v_ps_3548_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_ps_3548_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3552_ = v_ps_3548_;
v_isShared_3553_ = v_isSharedCheck_3558_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_state_3550_);
lean_inc(v_importedEntries_3549_);
lean_dec(v_ps_3548_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3558_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3547_, v_state_3550_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v___x_3554_);
v___x_3556_ = v___x_3552_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_importedEntries_3549_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3559_, lean_object* v_ps_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3559_, v_ps_3560_);
lean_dec(v_declName_3559_);
return v_res_3561_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___f_3605_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___x_3628_; lean_object* v_env_3629_; lean_object* v___x_3630_; 
lean_inc(v_declName_3565_);
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3605_, 0, v_declName_3565_);
v___x_3628_ = lean_st_ref_get(v___y_3571_);
v_env_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc_ref(v_env_3629_);
lean_dec(v___x_3628_);
v___x_3630_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3629_, v_declName_3565_);
lean_dec_ref(v_env_3629_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_dec(v_declName_3565_);
v___y_3607_ = v___y_3569_;
v___y_3608_ = v___y_3571_;
goto v___jp_3606_;
}
else
{
uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_dec_ref_known(v___x_3630_, 1);
lean_dec_ref(v___f_3605_);
v___x_3631_ = 0;
v___x_3632_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3633_ = l_Lean_MessageData_ofConstName(v_declName_3565_, v___x_3631_);
v___x_3634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3632_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3636_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
return v___x_3637_;
}
v___jp_3573_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_mctx_3589_; lean_object* v_zetaDeltaFVarIds_3590_; lean_object* v_postponed_3591_; lean_object* v_diag_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3603_; 
v___x_3585_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_3586_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3586_, 0, v___y_3584_);
lean_ctor_set(v___x_3586_, 1, v___y_3581_);
lean_ctor_set(v___x_3586_, 2, v___y_3579_);
lean_ctor_set(v___x_3586_, 3, v___y_3583_);
lean_ctor_set(v___x_3586_, 4, v___y_3582_);
lean_ctor_set(v___x_3586_, 5, v___x_3585_);
lean_ctor_set(v___x_3586_, 6, v___y_3575_);
lean_ctor_set(v___x_3586_, 7, v___y_3574_);
lean_ctor_set(v___x_3586_, 8, v___y_3577_);
lean_ctor_set(v___x_3586_, 9, v___y_3578_);
v___x_3587_ = lean_st_ref_put(v___y_3580_, v___x_3586_);
v___x_3588_ = lean_st_ref_take(v___y_3576_);
v_mctx_3589_ = lean_ctor_get(v___x_3588_, 0);
v_zetaDeltaFVarIds_3590_ = lean_ctor_get(v___x_3588_, 2);
v_postponed_3591_ = lean_ctor_get(v___x_3588_, 3);
v_diag_3592_ = lean_ctor_get(v___x_3588_, 4);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3588_, 1);
lean_dec(v_unused_3604_);
v___x_3594_ = v___x_3588_;
v_isShared_3595_ = v_isSharedCheck_3603_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_diag_3592_);
lean_inc(v_postponed_3591_);
lean_inc(v_zetaDeltaFVarIds_3590_);
lean_inc(v_mctx_3589_);
lean_dec(v___x_3588_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3603_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3596_ = lean_box(0);
v___x_3597_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 1, v___x_3597_);
v___x_3599_ = v___x_3594_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_mctx_3589_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_zetaDeltaFVarIds_3590_);
lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_postponed_3591_);
lean_ctor_set(v_reuseFailAlloc_3602_, 4, v_diag_3592_);
v___x_3599_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_st_ref_put(v___y_3576_, v___x_3599_);
v___x_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3596_);
return v___x_3601_;
}
}
}
v___jp_3606_:
{
lean_object* v___x_3609_; lean_object* v_env_3610_; lean_object* v_nextMacroScope_3611_; lean_object* v_ngen_3612_; lean_object* v_auxDeclNGen_3613_; lean_object* v_traceState_3614_; lean_object* v_recordedDeps_3615_; lean_object* v_messages_3616_; lean_object* v_infoState_3617_; lean_object* v_snapshotTasks_3618_; lean_object* v___x_3619_; lean_object* v_toEnvExtension_3620_; uint8_t v_logWrites_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3609_ = lean_st_ref_take(v___y_3608_);
v_env_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc_ref(v_env_3610_);
v_nextMacroScope_3611_ = lean_ctor_get(v___x_3609_, 1);
lean_inc(v_nextMacroScope_3611_);
v_ngen_3612_ = lean_ctor_get(v___x_3609_, 2);
lean_inc_ref(v_ngen_3612_);
v_auxDeclNGen_3613_ = lean_ctor_get(v___x_3609_, 3);
lean_inc_ref(v_auxDeclNGen_3613_);
v_traceState_3614_ = lean_ctor_get(v___x_3609_, 4);
lean_inc_ref(v_traceState_3614_);
v_recordedDeps_3615_ = lean_ctor_get(v___x_3609_, 6);
lean_inc_ref(v_recordedDeps_3615_);
v_messages_3616_ = lean_ctor_get(v___x_3609_, 7);
lean_inc_ref(v_messages_3616_);
v_infoState_3617_ = lean_ctor_get(v___x_3609_, 8);
lean_inc_ref(v_infoState_3617_);
v_snapshotTasks_3618_ = lean_ctor_get(v___x_3609_, 9);
lean_inc_ref(v_snapshotTasks_3618_);
lean_dec(v___x_3609_);
v___x_3619_ = l_Lean_docStringExt;
v_toEnvExtension_3620_ = lean_ctor_get(v___x_3619_, 0);
v_logWrites_3621_ = lean_ctor_get_uint8(v_toEnvExtension_3620_, sizeof(void*)*6);
v___x_3622_ = lean_box(2);
v___x_3623_ = lean_box(0);
v___x_3624_ = 1;
if (v_logWrites_3621_ == 0)
{
lean_object* v___x_3625_; 
lean_inc_ref(v_toEnvExtension_3620_);
v___x_3625_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3620_, v_env_3610_, v___f_3605_, v___x_3622_, v___x_3623_, v___x_3624_);
v___y_3574_ = v_messages_3616_;
v___y_3575_ = v_recordedDeps_3615_;
v___y_3576_ = v___y_3607_;
v___y_3577_ = v_infoState_3617_;
v___y_3578_ = v_snapshotTasks_3618_;
v___y_3579_ = v_ngen_3612_;
v___y_3580_ = v___y_3608_;
v___y_3581_ = v_nextMacroScope_3611_;
v___y_3582_ = v_traceState_3614_;
v___y_3583_ = v_auxDeclNGen_3613_;
v___y_3584_ = v___x_3625_;
goto v___jp_3573_;
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_inc_ref_n(v_toEnvExtension_3620_, 2);
v___x_3626_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3620_, v_env_3610_);
lean_dec_ref(v_env_3610_);
v___x_3627_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3620_, v___x_3626_, v___f_3605_, v___x_3622_, v___x_3623_, v___x_3624_);
v___y_3574_ = v_messages_3616_;
v___y_3575_ = v_recordedDeps_3615_;
v___y_3576_ = v___y_3607_;
v___y_3577_ = v_infoState_3617_;
v___y_3578_ = v_snapshotTasks_3618_;
v___y_3579_ = v_ngen_3612_;
v___y_3580_ = v___y_3608_;
v___y_3581_ = v_nextMacroScope_3611_;
v___y_3582_ = v_traceState_3614_;
v___y_3583_ = v_auxDeclNGen_3613_;
v___y_3584_ = v___x_3627_;
goto v___jp_3573_;
}
}
}
}
LEAN_EXPORT void l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3565_ = stack[0].m_obj;
lean_object* v___y_3566_ = stack[1].m_obj;
lean_object* v___y_3567_ = stack[2].m_obj;
lean_object* v___y_3568_ = stack[3].m_obj;
lean_object* v___y_3569_ = stack[4].m_obj;
lean_object* v___y_3570_ = stack[5].m_obj;
lean_object* v___y_3571_ = stack[6].m_obj;
lean_object* v_res_3638_;
v_res_3638_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
stack->m_obj
 = v_res_3638_;
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v_res_3647_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v___x_3668_; lean_object* v_env_3669_; lean_object* v_ref_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; 
v___x_3668_ = lean_st_ref_get(v_a_3666_);
v_env_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc_ref(v_env_3669_);
lean_dec(v___x_3668_);
v_ref_3670_ = lean_ctor_get(v_a_3665_, 2);
v___x_3671_ = 1;
lean_inc(v_declName_3660_);
v___x_3672_ = l_Lean_findInternalDocString_x3f(v_env_3669_, v_declName_3660_, v___x_3671_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
if (lean_obj_tag(v_a_3673_) == 1)
{
lean_object* v_val_3674_; 
v_val_3674_ = lean_ctor_get(v_a_3673_, 0);
lean_inc(v_val_3674_);
lean_dec_ref_known(v_a_3673_, 1);
if (lean_obj_tag(v_val_3674_) == 0)
{
lean_object* v_val_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3696_; 
v_val_3675_ = lean_ctor_get(v_val_3674_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_val_3674_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3677_ = v_val_3674_;
v_isShared_3678_ = v_isSharedCheck_3696_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_val_3675_);
lean_dec(v_val_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3696_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_removeBuiltinDocString(v_declName_3660_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3680_; 
lean_dec_ref_known(v___x_3679_, 1);
lean_del_object(v___x_3677_);
lean_inc(v_declName_3660_);
v___x_3680_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v___x_3681_; 
lean_dec_ref_known(v___x_3680_, 1);
v___x_3681_ = l_Lean_addVersoDocStringFromString(v_declName_3660_, v_val_3675_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
return v___x_3681_;
}
else
{
lean_dec(v_val_3675_);
lean_dec(v_declName_3660_);
return v___x_3680_;
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v_val_3675_);
lean_dec(v_declName_3660_);
v_a_3682_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3684_ = v___x_3679_;
v_isShared_3685_ = v_isSharedCheck_3695_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3679_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3695_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = lean_io_error_to_string(v_a_3682_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set_tag(v___x_3677_, 3);
lean_ctor_set(v___x_3677_, 0, v___x_3686_);
v___x_3688_ = v___x_3677_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = l_Lean_MessageData_ofFormat(v___x_3688_);
lean_inc(v_ref_3670_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_ref_3670_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3690_);
v___x_3692_ = v___x_3684_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
}
else
{
lean_object* v___x_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec(v_val_3674_);
v___x_3697_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3698_ = 0;
v___x_3699_ = l_Lean_MessageData_ofConstName(v_declName_3660_, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3697_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3702_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
return v___x_3703_;
}
}
else
{
lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_dec(v_a_3673_);
v___x_3704_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3705_ = 0;
v___x_3706_ = l_Lean_MessageData_ofConstName(v_declName_3660_, v___x_3705_);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3704_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3709_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
return v___x_3710_;
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v_declName_3660_);
v_a_3711_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3713_ = v___x_3672_;
v_isShared_3714_ = v_isSharedCheck_3722_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3672_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3722_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3715_ = lean_io_error_to_string(v_a_3711_);
v___x_3716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v___x_3717_ = l_Lean_MessageData_ofFormat(v___x_3716_);
lean_inc(v_ref_3670_);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_ref_3670_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3718_);
v___x_3720_ = v___x_3713_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_makeDocStringVerso_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3660_ = stack[0].m_obj;
lean_object* v_a_3661_ = stack[1].m_obj;
lean_object* v_a_3662_ = stack[2].m_obj;
lean_object* v_a_3663_ = stack[3].m_obj;
lean_object* v_a_3664_ = stack[4].m_obj;
lean_object* v_a_3665_ = stack[5].m_obj;
lean_object* v_a_3666_ = stack[6].m_obj;
lean_object* v_res_3723_;
v_res_3723_ = l_Lean_makeDocStringVerso(v_declName_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
stack->m_obj
 = v_res_3723_;
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_makeDocStringVerso(v_declName_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3733_, lean_object* v_k_3734_, lean_object* v_t_3735_, lean_object* v_h_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3734_, v_t_3735_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3738_, lean_object* v_k_3739_, lean_object* v_t_3740_, lean_object* v_h_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3738_, v_k_3739_, v_t_3740_, v_h_3741_);
lean_dec(v_k_3739_);
return v_res_3742_;
}
}
lean_object* l_Lean_addDocString(lean_object* v_declName_3743_, lean_object* v_binders_3744_, lean_object* v_docComment_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
uint8_t v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = l_Lean_isVersoDocComment(v_docComment_3745_);
v___x_3754_ = l_Lean_addDocStringOf(v___x_3753_, v_declName_3743_, v_binders_3744_, v_docComment_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3754_;
}
}
LEAN_EXPORT void l_Lean_addDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3743_ = stack[0].m_obj;
lean_object* v_binders_3744_ = stack[1].m_obj;
lean_object* v_docComment_3745_ = stack[2].m_obj;
lean_object* v_a_3746_ = stack[3].m_obj;
lean_object* v_a_3747_ = stack[4].m_obj;
lean_object* v_a_3748_ = stack[5].m_obj;
lean_object* v_a_3749_ = stack[6].m_obj;
lean_object* v_a_3750_ = stack[7].m_obj;
lean_object* v_a_3751_ = stack[8].m_obj;
lean_object* v_res_3755_;
v_res_3755_ = l_Lean_addDocString(v_declName_3743_, v_binders_3744_, v_docComment_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
stack->m_obj
 = v_res_3755_;
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3756_, lean_object* v_binders_3757_, lean_object* v_docComment_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_addDocString(v_declName_3756_, v_binders_3757_, v_docComment_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
return v_res_3766_;
}
}
lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3767_, lean_object* v_binders_3768_, lean_object* v_docString_x3f_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3769_) == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_dec(v_binders_3768_);
lean_dec(v_declName_3767_);
v___x_3777_ = lean_box(0);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v_val_3779_; lean_object* v___x_3780_; 
v_val_3779_ = lean_ctor_get(v_docString_x3f_3769_, 0);
lean_inc(v_val_3779_);
lean_dec_ref_known(v_docString_x3f_3769_, 1);
v___x_3780_ = l_Lean_addDocString(v_declName_3767_, v_binders_3768_, v_val_3779_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
return v___x_3780_;
}
}
}
LEAN_EXPORT void l_Lean_addDocString_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3767_ = stack[0].m_obj;
lean_object* v_binders_3768_ = stack[1].m_obj;
lean_object* v_docString_x3f_3769_ = stack[2].m_obj;
lean_object* v_a_3770_ = stack[3].m_obj;
lean_object* v_a_3771_ = stack[4].m_obj;
lean_object* v_a_3772_ = stack[5].m_obj;
lean_object* v_a_3773_ = stack[6].m_obj;
lean_object* v_a_3774_ = stack[7].m_obj;
lean_object* v_a_3775_ = stack[8].m_obj;
lean_object* v_res_3781_;
v_res_3781_ = l_Lean_addDocString_x27(v_declName_3767_, v_binders_3768_, v_docString_x3f_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
stack->m_obj
 = v_res_3781_;
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3782_, lean_object* v_binders_3783_, lean_object* v_docString_x3f_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_addDocString_x27(v_declName_3782_, v_binders_3783_, v_docString_x3f_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
return v_res_3792_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; lean_object* v_nextMacroScope_3798_; lean_object* v_ngen_3799_; lean_object* v_auxDeclNGen_3800_; lean_object* v_traceState_3801_; lean_object* v_recordedDeps_3802_; lean_object* v_messages_3803_; lean_object* v_infoState_3804_; lean_object* v_snapshotTasks_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3831_; 
v___x_3797_ = lean_st_ref_take(v___y_3795_);
v_nextMacroScope_3798_ = lean_ctor_get(v___x_3797_, 1);
v_ngen_3799_ = lean_ctor_get(v___x_3797_, 2);
v_auxDeclNGen_3800_ = lean_ctor_get(v___x_3797_, 3);
v_traceState_3801_ = lean_ctor_get(v___x_3797_, 4);
v_recordedDeps_3802_ = lean_ctor_get(v___x_3797_, 6);
v_messages_3803_ = lean_ctor_get(v___x_3797_, 7);
v_infoState_3804_ = lean_ctor_get(v___x_3797_, 8);
v_snapshotTasks_3805_ = lean_ctor_get(v___x_3797_, 9);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3831_ == 0)
{
lean_object* v_unused_3832_; lean_object* v_unused_3833_; 
v_unused_3832_ = lean_ctor_get(v___x_3797_, 5);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v___x_3797_, 0);
lean_dec(v_unused_3833_);
v___x_3807_ = v___x_3797_;
v_isShared_3808_ = v_isSharedCheck_3831_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_snapshotTasks_3805_);
lean_inc(v_infoState_3804_);
lean_inc(v_messages_3803_);
lean_inc(v_recordedDeps_3802_);
lean_inc(v_traceState_3801_);
lean_inc(v_auxDeclNGen_3800_);
lean_inc(v_ngen_3799_);
lean_inc(v_nextMacroScope_3798_);
lean_dec(v___x_3797_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3831_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3809_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 5, v___x_3809_);
lean_ctor_set(v___x_3807_, 0, v_env_3793_);
v___x_3811_ = v___x_3807_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_env_3793_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_nextMacroScope_3798_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_ngen_3799_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_auxDeclNGen_3800_);
lean_ctor_set(v_reuseFailAlloc_3830_, 4, v_traceState_3801_);
lean_ctor_set(v_reuseFailAlloc_3830_, 5, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3830_, 6, v_recordedDeps_3802_);
lean_ctor_set(v_reuseFailAlloc_3830_, 7, v_messages_3803_);
lean_ctor_set(v_reuseFailAlloc_3830_, 8, v_infoState_3804_);
lean_ctor_set(v_reuseFailAlloc_3830_, 9, v_snapshotTasks_3805_);
v___x_3811_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v_mctx_3814_; lean_object* v_zetaDeltaFVarIds_3815_; lean_object* v_postponed_3816_; lean_object* v_diag_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3828_; 
v___x_3812_ = lean_st_ref_put(v___y_3795_, v___x_3811_);
v___x_3813_ = lean_st_ref_take(v___y_3794_);
v_mctx_3814_ = lean_ctor_get(v___x_3813_, 0);
v_zetaDeltaFVarIds_3815_ = lean_ctor_get(v___x_3813_, 2);
v_postponed_3816_ = lean_ctor_get(v___x_3813_, 3);
v_diag_3817_ = lean_ctor_get(v___x_3813_, 4);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; 
v_unused_3829_ = lean_ctor_get(v___x_3813_, 1);
lean_dec(v_unused_3829_);
v___x_3819_ = v___x_3813_;
v_isShared_3820_ = v_isSharedCheck_3828_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_diag_3817_);
lean_inc(v_postponed_3816_);
lean_inc(v_zetaDeltaFVarIds_3815_);
lean_inc(v_mctx_3814_);
lean_dec(v___x_3813_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3828_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3821_ = lean_box(0);
v___x_3822_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 1, v___x_3822_);
v___x_3824_ = v___x_3819_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_mctx_3814_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_zetaDeltaFVarIds_3815_);
lean_ctor_set(v_reuseFailAlloc_3827_, 3, v_postponed_3816_);
lean_ctor_set(v_reuseFailAlloc_3827_, 4, v_diag_3817_);
v___x_3824_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = lean_st_ref_put(v___y_3794_, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3821_);
return v___x_3826_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3793_ = stack[0].m_obj;
lean_object* v___y_3794_ = stack[1].m_obj;
lean_object* v___y_3795_ = stack[2].m_obj;
lean_object* v_res_3834_;
v_res_3834_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3793_, v___y_3794_, v___y_3795_);
stack->m_obj
 = v_res_3834_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
return v_res_3839_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3840_, uint8_t v___x_3841_, lean_object* v_as_3842_, size_t v_i_3843_, size_t v_stop_3844_, lean_object* v_b_3845_){
_start:
{
lean_object* v___y_3847_; uint8_t v___x_3851_; 
v___x_3851_ = lean_usize_dec_eq(v_i_3843_, v_stop_3844_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; lean_object* v_index_3853_; lean_object* v_sourceString_3854_; lean_object* v_imports_3855_; lean_object* v_currNamespace_3856_; lean_object* v_openDecls_3857_; lean_object* v_options_3858_; lean_object* v_check_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3876_; 
v___x_3852_ = lean_array_uget(v_as_3842_, v_i_3843_);
v_index_3853_ = lean_ctor_get(v___x_3852_, 1);
v_sourceString_3854_ = lean_ctor_get(v___x_3852_, 2);
v_imports_3855_ = lean_ctor_get(v___x_3852_, 3);
v_currNamespace_3856_ = lean_ctor_get(v___x_3852_, 4);
v_openDecls_3857_ = lean_ctor_get(v___x_3852_, 5);
v_options_3858_ = lean_ctor_get(v___x_3852_, 6);
v_check_3859_ = lean_ctor_get(v___x_3852_, 7);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; 
v_unused_3877_ = lean_ctor_get(v___x_3852_, 0);
lean_dec(v_unused_3877_);
v___x_3861_ = v___x_3852_;
v_isShared_3862_ = v_isSharedCheck_3876_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_check_3859_);
lean_inc(v_options_3858_);
lean_inc(v_openDecls_3857_);
lean_inc(v_currNamespace_3856_);
lean_inc(v_imports_3855_);
lean_inc(v_sourceString_3854_);
lean_inc(v_index_3853_);
lean_dec(v___x_3852_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3876_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; lean_object* v_toEnvExtension_3864_; lean_object* v_asyncMode_3865_; uint8_t v_logWrites_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3863_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3864_ = lean_ctor_get(v___x_3863_, 0);
v_asyncMode_3865_ = lean_ctor_get(v_toEnvExtension_3864_, 2);
v_logWrites_3866_ = lean_ctor_get_uint8(v_toEnvExtension_3864_, sizeof(void*)*6);
lean_inc(v_n_3840_);
v___x_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3867_, 0, v_n_3840_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3867_);
v___x_3869_ = v___x_3861_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_index_3853_);
lean_ctor_set(v_reuseFailAlloc_3875_, 2, v_sourceString_3854_);
lean_ctor_set(v_reuseFailAlloc_3875_, 3, v_imports_3855_);
lean_ctor_set(v_reuseFailAlloc_3875_, 4, v_currNamespace_3856_);
lean_ctor_set(v_reuseFailAlloc_3875_, 5, v_openDecls_3857_);
lean_ctor_set(v_reuseFailAlloc_3875_, 6, v_options_3858_);
lean_ctor_set(v_reuseFailAlloc_3875_, 7, v_check_3859_);
v___x_3869_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___f_3870_; lean_object* v___x_3871_; 
v___f_3870_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_3870_, 0, v___x_3863_);
lean_closure_set(v___f_3870_, 1, v___x_3869_);
v___x_3871_ = lean_box(0);
if (v_logWrites_3866_ == 0)
{
lean_object* v___x_3872_; 
lean_inc_ref(v_toEnvExtension_3864_);
v___x_3872_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3864_, v_b_3845_, v___f_3870_, v_asyncMode_3865_, v___x_3871_, v___x_3841_);
v___y_3847_ = v___x_3872_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_inc_ref_n(v_toEnvExtension_3864_, 2);
v___x_3873_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3864_, v_b_3845_);
lean_dec_ref(v_b_3845_);
v___x_3874_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3864_, v___x_3873_, v___f_3870_, v_asyncMode_3865_, v___x_3871_, v___x_3841_);
v___y_3847_ = v___x_3874_;
goto v___jp_3846_;
}
}
}
}
else
{
lean_dec(v_n_3840_);
return v_b_3845_;
}
v___jp_3846_:
{
size_t v___x_3848_; size_t v___x_3849_; 
v___x_3848_ = ((size_t)1ULL);
v___x_3849_ = lean_usize_add(v_i_3843_, v___x_3848_);
v_i_3843_ = v___x_3849_;
v_b_3845_ = v___y_3847_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3840_ = stack[0].m_obj;
uint8_t v___x_3841_ = stack[1].m_num;
lean_object* v_as_3842_ = stack[2].m_obj;
size_t v_i_3843_ = stack[3].m_num;
size_t v_stop_3844_ = stack[4].m_num;
lean_object* v_b_3845_ = stack[5].m_obj;
lean_object* v_res_3878_;
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3840_, v___x_3841_, v_as_3842_, v_i_3843_, v_stop_3844_, v_b_3845_);
stack->m_obj
 = v_res_3878_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3879_, lean_object* v___x_3880_, lean_object* v_as_3881_, lean_object* v_i_3882_, lean_object* v_stop_3883_, lean_object* v_b_3884_){
_start:
{
uint8_t v___x_1382__boxed_3885_; size_t v_i_boxed_3886_; size_t v_stop_boxed_3887_; lean_object* v_res_3888_; 
v___x_1382__boxed_3885_ = lean_unbox(v___x_3880_);
v_i_boxed_3886_ = lean_unbox_usize(v_i_3882_);
lean_dec(v_i_3882_);
v_stop_boxed_3887_ = lean_unbox_usize(v_stop_3883_);
lean_dec(v_stop_3883_);
v_res_3888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3879_, v___x_1382__boxed_3885_, v_as_3881_, v_i_boxed_3886_, v_stop_boxed_3887_, v_b_3884_);
lean_dec_ref(v_as_3881_);
return v_res_3888_;
}
}
lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3889_, lean_object* v_deferred_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___x_3898_; lean_object* v_env_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3898_ = lean_st_ref_get(v___y_3896_);
v_env_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc_ref(v_env_3899_);
lean_dec(v___x_3898_);
v___x_3900_ = l_Lean_getMainModuleDoc(v_env_3899_);
v___x_3901_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3900_);
lean_dec_ref(v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec_ref(v_docs_3889_);
v___x_3902_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3903_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3902_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
return v___x_3903_;
}
else
{
lean_object* v___x_3904_; lean_object* v_env_3905_; lean_object* v___x_3906_; lean_object* v_size_3907_; lean_object* v___x_3908_; lean_object* v_env_3909_; lean_object* v___x_3910_; 
v___x_3904_ = lean_st_ref_get(v___y_3896_);
v_env_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc_ref(v_env_3905_);
lean_dec(v___x_3904_);
v___x_3906_ = l_Lean_getMainVersoModuleDocs(v_env_3905_);
v_size_3907_ = lean_ctor_get(v___x_3906_, 2);
lean_inc(v_size_3907_);
lean_dec_ref(v___x_3906_);
v___x_3908_ = lean_st_ref_get(v___y_3896_);
v_env_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc_ref(v_env_3909_);
lean_dec(v___x_3908_);
v___x_3910_ = l_Lean_addVersoModuleDocSnippet(v_env_3909_, v_docs_3889_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec(v_size_3907_);
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_3913_ = l_Lean_stringToMessageData(v_a_3911_);
v___x_3914_ = l_Lean_indentD(v___x_3913_);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3912_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3915_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
return v___x_3916_;
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_a_3917_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = lean_array_get_size(v_deferred_3890_);
v___x_3920_ = lean_nat_dec_lt(v___x_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
lean_dec(v_size_3907_);
v___x_3921_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3917_, v___y_3894_, v___y_3896_);
return v___x_3921_;
}
else
{
size_t v___x_3922_; size_t v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3922_ = ((size_t)0ULL);
v___x_3923_ = lean_usize_of_nat(v___x_3919_);
v___x_3924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3907_, v___x_3901_, v_deferred_3890_, v___x_3922_, v___x_3923_, v_a_3917_);
v___x_3925_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3924_, v___y_3894_, v___y_3896_);
return v___x_3925_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_docs_3889_ = stack[0].m_obj;
lean_object* v_deferred_3890_ = stack[1].m_obj;
lean_object* v___y_3891_ = stack[2].m_obj;
lean_object* v___y_3892_ = stack[3].m_obj;
lean_object* v___y_3893_ = stack[4].m_obj;
lean_object* v___y_3894_ = stack[5].m_obj;
lean_object* v___y_3895_ = stack[6].m_obj;
lean_object* v___y_3896_ = stack[7].m_obj;
lean_object* v_res_3926_;
v_res_3926_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3889_, v_deferred_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
stack->m_obj
 = v_res_3926_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3927_, lean_object* v_deferred_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3927_, v_deferred_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec_ref(v_deferred_3928_);
return v_res_3936_;
}
}
lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3937_, lean_object* v_doc_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_versoModDocString(v_range_3937_, v_doc_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v_fst_3948_; lean_object* v_snd_3949_; lean_object* v___x_3950_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v_fst_3948_ = lean_ctor_get(v_a_3947_, 0);
lean_inc(v_fst_3948_);
v_snd_3949_ = lean_ctor_get(v_a_3947_, 1);
lean_inc(v_snd_3949_);
lean_dec(v_a_3947_);
v___x_3950_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3948_, v_snd_3949_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_snd_3949_);
return v___x_3950_;
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
v_a_3951_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3946_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3946_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addVersoModDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_3937_ = stack[0].m_obj;
lean_object* v_doc_3938_ = stack[1].m_obj;
lean_object* v_a_3939_ = stack[2].m_obj;
lean_object* v_a_3940_ = stack[3].m_obj;
lean_object* v_a_3941_ = stack[4].m_obj;
lean_object* v_a_3942_ = stack[5].m_obj;
lean_object* v_a_3943_ = stack[6].m_obj;
lean_object* v_a_3944_ = stack[7].m_obj;
lean_object* v_res_3959_;
v_res_3959_ = l_Lean_addVersoModDocString(v_range_3937_, v_doc_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
stack->m_obj
 = v_res_3959_;
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3960_, lean_object* v_doc_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_addVersoModDocString(v_range_3960_, v_doc_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_doc_3961_);
return v_res_3969_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3970_, v___y_3974_, v___y_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3970_ = stack[0].m_obj;
lean_object* v___y_3971_ = stack[1].m_obj;
lean_object* v___y_3972_ = stack[2].m_obj;
lean_object* v___y_3973_ = stack[3].m_obj;
lean_object* v___y_3974_ = stack[4].m_obj;
lean_object* v___y_3975_ = stack[5].m_obj;
lean_object* v___y_3976_ = stack[6].m_obj;
lean_object* v_res_3979_;
v_res_3979_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
stack->m_obj
 = v_res_3979_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
return v_res_3988_;
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
