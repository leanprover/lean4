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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v_toCold_684_; lean_object* v_val_685_; lean_object* v_currRecDepth_686_; lean_object* v_ref_687_; uint16_t v_optionFlags_688_; uint8_t v_suppressElabErrors_689_; uint8_t v_checkDeprecated_690_; uint8_t v_isRecordingDeps_691_; lean_object* v_fileName_692_; lean_object* v_options_693_; lean_object* v_maxRecDepth_694_; lean_object* v_currNamespace_695_; lean_object* v_openDecls_696_; lean_object* v_initHeartbeats_697_; lean_object* v_maxHeartbeats_698_; lean_object* v_quotContext_699_; lean_object* v_currMacroScope_700_; lean_object* v_cancelTk_x3f_701_; lean_object* v_inheritedTraceOptions_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_toCold_684_ = lean_ctor_get(v___y_680_, 0);
v_val_685_ = lean_ctor_get(v_fileMap_x3f_671_, 0);
v_currRecDepth_686_ = lean_ctor_get(v___y_680_, 1);
v_ref_687_ = lean_ctor_get(v___y_680_, 2);
v_optionFlags_688_ = lean_ctor_get_uint16(v___y_680_, sizeof(void*)*3);
v_suppressElabErrors_689_ = lean_ctor_get_uint8(v___y_680_, sizeof(void*)*3 + 2);
v_checkDeprecated_690_ = lean_ctor_get_uint8(v___y_680_, sizeof(void*)*3 + 3);
v_isRecordingDeps_691_ = lean_ctor_get_uint8(v___y_680_, sizeof(void*)*3 + 4);
v_fileName_692_ = lean_ctor_get(v_toCold_684_, 0);
v_options_693_ = lean_ctor_get(v_toCold_684_, 2);
v_maxRecDepth_694_ = lean_ctor_get(v_toCold_684_, 3);
v_currNamespace_695_ = lean_ctor_get(v_toCold_684_, 4);
v_openDecls_696_ = lean_ctor_get(v_toCold_684_, 5);
v_initHeartbeats_697_ = lean_ctor_get(v_toCold_684_, 6);
v_maxHeartbeats_698_ = lean_ctor_get(v_toCold_684_, 7);
v_quotContext_699_ = lean_ctor_get(v_toCold_684_, 8);
v_currMacroScope_700_ = lean_ctor_get(v_toCold_684_, 9);
v_cancelTk_x3f_701_ = lean_ctor_get(v_toCold_684_, 10);
v_inheritedTraceOptions_702_ = lean_ctor_get(v_toCold_684_, 11);
lean_inc_ref(v_inheritedTraceOptions_702_);
lean_inc(v_cancelTk_x3f_701_);
lean_inc(v_currMacroScope_700_);
lean_inc(v_quotContext_699_);
lean_inc(v_maxHeartbeats_698_);
lean_inc(v_initHeartbeats_697_);
lean_inc(v_openDecls_696_);
lean_inc(v_currNamespace_695_);
lean_inc(v_maxRecDepth_694_);
lean_inc_ref(v_options_693_);
lean_inc(v_val_685_);
lean_inc_ref(v_fileName_692_);
v___x_703_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_703_, 0, v_fileName_692_);
lean_ctor_set(v___x_703_, 1, v_val_685_);
lean_ctor_set(v___x_703_, 2, v_options_693_);
lean_ctor_set(v___x_703_, 3, v_maxRecDepth_694_);
lean_ctor_set(v___x_703_, 4, v_currNamespace_695_);
lean_ctor_set(v___x_703_, 5, v_openDecls_696_);
lean_ctor_set(v___x_703_, 6, v_initHeartbeats_697_);
lean_ctor_set(v___x_703_, 7, v_maxHeartbeats_698_);
lean_ctor_set(v___x_703_, 8, v_quotContext_699_);
lean_ctor_set(v___x_703_, 9, v_currMacroScope_700_);
lean_ctor_set(v___x_703_, 10, v_cancelTk_x3f_701_);
lean_ctor_set(v___x_703_, 11, v_inheritedTraceOptions_702_);
lean_inc(v_ref_687_);
lean_inc(v_currRecDepth_686_);
v___x_704_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_currRecDepth_686_);
lean_ctor_set(v___x_704_, 2, v_ref_687_);
lean_ctor_set_uint16(v___x_704_, sizeof(void*)*3, v_optionFlags_688_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*3 + 2, v_suppressElabErrors_689_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*3 + 3, v_checkDeprecated_690_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*3 + 4, v_isRecordingDeps_691_);
v___x_705_ = l_Lean_Doc_DocM_exec___redArg(v_declName_672_, v_binders_673_, v___x_674_, v___x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___x_704_, v___y_681_);
lean_dec_ref_known(v___x_704_, 3);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_706_, lean_object* v_declName_707_, lean_object* v_binders_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_9873__boxed_718_; lean_object* v_res_719_; 
v___x_9873__boxed_718_ = lean_unbox(v___x_710_);
v_res_719_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_706_, v_declName_707_, v_binders_708_, v___x_709_, v___x_9873__boxed_718_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v_fileMap_x3f_706_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_720_, size_t v_i_721_, lean_object* v_bs_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_usize_dec_lt(v_i_721_, v_sz_720_);
if (v___x_723_ == 0)
{
return v_bs_722_;
}
else
{
lean_object* v_v_724_; lean_object* v___x_725_; lean_object* v_bs_x27_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v_v_724_ = lean_array_uget(v_bs_722_, v_i_721_);
v___x_725_ = lean_unsigned_to_nat(0u);
v_bs_x27_726_ = lean_array_uset(v_bs_722_, v_i_721_, v___x_725_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_721_, v___x_727_);
v___x_729_ = lean_array_uset(v_bs_x27_726_, v_i_721_, v_v_724_);
v_i_721_ = v___x_728_;
v_bs_722_ = v___x_729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_bs_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_735_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_734_, v_i_boxed_735_, v_bs_733_);
return v_res_736_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_737_, lean_object* v_opt_738_){
_start:
{
lean_object* v_name_739_; lean_object* v_defValue_740_; lean_object* v_map_741_; lean_object* v___x_742_; 
v_name_739_ = lean_ctor_get(v_opt_738_, 0);
v_defValue_740_ = lean_ctor_get(v_opt_738_, 1);
v_map_741_ = lean_ctor_get(v_opts_737_, 0);
v___x_742_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_741_, v_name_739_);
if (lean_obj_tag(v___x_742_) == 0)
{
uint8_t v___x_743_; 
v___x_743_ = lean_unbox(v_defValue_740_);
return v___x_743_;
}
else
{
lean_object* v_val_744_; 
v_val_744_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_742_, 1);
if (lean_obj_tag(v_val_744_) == 1)
{
uint8_t v_v_745_; 
v_v_745_ = lean_ctor_get_uint8(v_val_744_, 0);
lean_dec_ref_known(v_val_744_, 0);
return v_v_745_;
}
else
{
uint8_t v___x_746_; 
lean_dec(v_val_744_);
v___x_746_ = lean_unbox(v_defValue_740_);
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_747_, lean_object* v_opt_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_747_, v_opt_748_);
lean_dec_ref(v_opt_748_);
lean_dec_ref(v_opts_747_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; lean_object* v_env_758_; uint8_t v___x_759_; lean_object* v_env_760_; lean_object* v___x_761_; lean_object* v_toCold_762_; lean_object* v_mctx_763_; lean_object* v_lctx_764_; lean_object* v_options_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_757_ = lean_st_ref_get(v___y_755_);
v_env_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc_ref(v_env_758_);
lean_dec(v___x_757_);
v___x_759_ = 0;
v_env_760_ = l_Lean_Environment_setRecordingDeps(v_env_758_, v___x_759_);
v___x_761_ = lean_st_ref_get(v___y_753_);
v_toCold_762_ = lean_ctor_get(v___y_754_, 0);
v_mctx_763_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_mctx_763_);
lean_dec(v___x_761_);
v_lctx_764_ = lean_ctor_get(v___y_752_, 2);
v_options_765_ = lean_ctor_get(v_toCold_762_, 2);
lean_inc_ref(v_options_765_);
lean_inc_ref(v_lctx_764_);
v___x_766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_766_, 0, v_env_760_);
lean_ctor_set(v___x_766_, 1, v_mctx_763_);
lean_ctor_set(v___x_766_, 2, v_lctx_764_);
lean_ctor_set(v___x_766_, 3, v_options_765_);
v___x_767_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_msgData_751_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_776_, lean_object* v_x_777_){
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
return v_suppressElabErrors_776_;
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
return v_suppressElabErrors_776_;
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
return v_suppressElabErrors_776_;
}
}
}
}
else
{
uint8_t v___x_800_; 
v___x_800_ = 0;
return v___x_800_;
}
}
default: 
{
uint8_t v___x_801_; 
v___x_801_ = 0;
return v___x_801_;
}
}
}
case 0:
{
lean_object* v_str_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_str_802_ = lean_ctor_get(v_x_777_, 1);
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_804_ = lean_string_dec_eq(v_str_802_, v___x_803_);
if (v___x_804_ == 0)
{
return v___x_804_;
}
else
{
return v_suppressElabErrors_776_;
}
}
default: 
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
}
}
else
{
uint8_t v___x_806_; 
v___x_806_ = 0;
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_807_, lean_object* v_x_808_){
_start:
{
uint8_t v_suppressElabErrors_boxed_809_; uint8_t v_res_810_; lean_object* v_r_811_; 
v_suppressElabErrors_boxed_809_ = lean_unbox(v_suppressElabErrors_807_);
v_res_810_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_809_, v_x_808_);
lean_dec(v_x_808_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_812_, lean_object* v_msgData_813_, uint8_t v_severity_814_, uint8_t v_isSilent_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___y_822_; uint8_t v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v_toCold_829_; lean_object* v___y_830_; lean_object* v___y_859_; lean_object* v___y_860_; uint8_t v___y_861_; uint8_t v___y_862_; uint8_t v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; uint8_t v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; uint8_t v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; uint8_t v___y_896_; uint8_t v___y_897_; uint8_t v___x_907_; uint8_t v___y_909_; uint8_t v___x_915_; 
v___x_907_ = 2;
v___x_915_ = l_Lean_instBEqMessageSeverity_beq(v_severity_814_, v___x_907_);
if (v___x_915_ == 0)
{
v___y_909_ = v___x_915_;
goto v___jp_908_;
}
else
{
uint8_t v___x_916_; 
lean_inc_ref(v_msgData_813_);
v___x_916_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_813_);
if (v___x_916_ == 0)
{
v___y_909_ = v___x_916_;
goto v___jp_908_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v_msgData_813_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
v___jp_821_:
{
lean_object* v_currNamespace_831_; lean_object* v_openDecls_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_env_837_; lean_object* v_nextMacroScope_838_; lean_object* v_ngen_839_; lean_object* v_auxDeclNGen_840_; lean_object* v_traceState_841_; lean_object* v_cache_842_; lean_object* v_recordedDeps_843_; lean_object* v_messages_844_; lean_object* v_infoState_845_; lean_object* v_snapshotTasks_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_857_; 
v_currNamespace_831_ = lean_ctor_get(v_toCold_829_, 4);
v_openDecls_832_ = lean_ctor_get(v_toCold_829_, 5);
lean_inc(v_openDecls_832_);
lean_inc(v_currNamespace_831_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_currNamespace_831_);
lean_ctor_set(v___x_833_, 1, v_openDecls_832_);
v___x_834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___y_825_);
lean_inc_ref(v___y_827_);
lean_inc_ref(v___y_828_);
v___x_835_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_835_, 0, v___y_828_);
lean_ctor_set(v___x_835_, 1, v___y_822_);
lean_ctor_set(v___x_835_, 2, v___y_824_);
lean_ctor_set(v___x_835_, 3, v___y_827_);
lean_ctor_set(v___x_835_, 4, v___x_834_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*5, v___y_823_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*5 + 1, v___y_826_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*5 + 2, v_isSilent_815_);
v___x_836_ = lean_st_ref_take(v___y_830_);
v_env_837_ = lean_ctor_get(v___x_836_, 0);
v_nextMacroScope_838_ = lean_ctor_get(v___x_836_, 1);
v_ngen_839_ = lean_ctor_get(v___x_836_, 2);
v_auxDeclNGen_840_ = lean_ctor_get(v___x_836_, 3);
v_traceState_841_ = lean_ctor_get(v___x_836_, 4);
v_cache_842_ = lean_ctor_get(v___x_836_, 5);
v_recordedDeps_843_ = lean_ctor_get(v___x_836_, 6);
v_messages_844_ = lean_ctor_get(v___x_836_, 7);
v_infoState_845_ = lean_ctor_get(v___x_836_, 8);
v_snapshotTasks_846_ = lean_ctor_get(v___x_836_, 9);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_857_ == 0)
{
v___x_848_ = v___x_836_;
v_isShared_849_ = v_isSharedCheck_857_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_snapshotTasks_846_);
lean_inc(v_infoState_845_);
lean_inc(v_messages_844_);
lean_inc(v_recordedDeps_843_);
lean_inc(v_cache_842_);
lean_inc(v_traceState_841_);
lean_inc(v_auxDeclNGen_840_);
lean_inc(v_ngen_839_);
lean_inc(v_nextMacroScope_838_);
lean_inc(v_env_837_);
lean_dec(v___x_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_857_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_box(0);
v___x_851_ = l_Lean_MessageLog_add(v___x_835_, v_messages_844_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 7, v___x_851_);
v___x_853_ = v___x_848_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_env_837_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_nextMacroScope_838_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_ngen_839_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_auxDeclNGen_840_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v_traceState_841_);
lean_ctor_set(v_reuseFailAlloc_856_, 5, v_cache_842_);
lean_ctor_set(v_reuseFailAlloc_856_, 6, v_recordedDeps_843_);
lean_ctor_set(v_reuseFailAlloc_856_, 7, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_856_, 8, v_infoState_845_);
lean_ctor_set(v_reuseFailAlloc_856_, 9, v_snapshotTasks_846_);
v___x_853_ = v_reuseFailAlloc_856_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_st_ref_put(v___y_830_, v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_850_);
return v___x_855_;
}
}
}
v___jp_858_:
{
lean_object* v_fileName_867_; lean_object* v_fileMap_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_884_; 
v_fileName_867_ = lean_ctor_get(v___y_865_, 0);
v_fileMap_868_ = lean_ctor_get(v___y_865_, 1);
v___x_869_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_813_);
v___x_870_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_869_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_884_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_inc_ref_n(v_fileMap_868_, 2);
v___x_875_ = l_Lean_FileMap_toPosition(v_fileMap_868_, v___y_864_);
lean_dec(v___y_864_);
v___x_876_ = l_Lean_FileMap_toPosition(v_fileMap_868_, v___y_866_);
lean_dec(v___y_866_);
v___x_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_861_ == 0)
{
lean_del_object(v___x_873_);
lean_dec_ref(v___y_859_);
v___y_822_ = v___x_875_;
v___y_823_ = v___y_862_;
v___y_824_ = v___x_877_;
v___y_825_ = v_a_871_;
v___y_826_ = v___y_863_;
v___y_827_ = v___x_878_;
v___y_828_ = v_fileName_867_;
v_toCold_829_ = v___y_860_;
v___y_830_ = v___y_819_;
goto v___jp_821_;
}
else
{
uint8_t v___x_879_; 
lean_inc(v_a_871_);
v___x_879_ = l_Lean_MessageData_hasTag(v___y_859_, v_a_871_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_882_; 
lean_dec_ref_known(v___x_877_, 1);
lean_dec_ref(v___x_875_);
lean_dec(v_a_871_);
v___x_880_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_880_);
v___x_882_ = v___x_873_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
lean_del_object(v___x_873_);
v___y_822_ = v___x_875_;
v___y_823_ = v___y_862_;
v___y_824_ = v___x_877_;
v___y_825_ = v_a_871_;
v___y_826_ = v___y_863_;
v___y_827_ = v___x_878_;
v___y_828_ = v_fileName_867_;
v_toCold_829_ = v___y_860_;
v___y_830_ = v___y_819_;
goto v___jp_821_;
}
}
}
}
v___jp_885_:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Syntax_getTailPos_x3f(v___y_891_, v___y_889_);
lean_dec(v___y_891_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_inc(v___y_892_);
v___y_859_ = v___y_887_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_886_;
v___y_862_ = v___y_889_;
v___y_863_ = v___y_890_;
v___y_864_ = v___y_892_;
v___y_865_ = v___y_888_;
v___y_866_ = v___y_892_;
goto v___jp_858_;
}
else
{
lean_object* v_val_894_; 
v_val_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v___x_893_, 1);
v___y_859_ = v___y_887_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_886_;
v___y_862_ = v___y_889_;
v___y_863_ = v___y_890_;
v___y_864_ = v___y_892_;
v___y_865_ = v___y_888_;
v___y_866_ = v_val_894_;
goto v___jp_858_;
}
}
v___jp_895_:
{
lean_object* v_toCold_898_; lean_object* v_ref_899_; uint8_t v_suppressElabErrors_900_; lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v_ref_903_; lean_object* v___x_904_; 
v_toCold_898_ = lean_ctor_get(v___y_818_, 0);
v_ref_899_ = lean_ctor_get(v___y_818_, 2);
v_suppressElabErrors_900_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3 + 2);
v___x_901_ = lean_box(v_suppressElabErrors_900_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_902_, 0, v___x_901_);
v_ref_903_ = l_Lean_replaceRef(v_ref_812_, v_ref_899_);
v___x_904_ = l_Lean_Syntax_getPos_x3f(v_ref_903_, v___y_896_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___y_886_ = v_suppressElabErrors_900_;
v___y_887_ = v___f_902_;
v___y_888_ = v_toCold_898_;
v___y_889_ = v___y_896_;
v___y_890_ = v___y_897_;
v___y_891_ = v_ref_903_;
v___y_892_ = v___x_905_;
goto v___jp_885_;
}
else
{
lean_object* v_val_906_; 
v_val_906_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_904_, 1);
v___y_886_ = v_suppressElabErrors_900_;
v___y_887_ = v___f_902_;
v___y_888_ = v_toCold_898_;
v___y_889_ = v___y_896_;
v___y_890_ = v___y_897_;
v___y_891_ = v_ref_903_;
v___y_892_ = v_val_906_;
goto v___jp_885_;
}
}
v___jp_908_:
{
uint8_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 1;
v___x_911_ = l_Lean_instBEqMessageSeverity_beq(v_severity_814_, v___x_910_);
if (v___x_911_ == 0)
{
v___y_896_ = v___y_909_;
v___y_897_ = v_severity_814_;
goto v___jp_895_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_912_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_818_);
v___x_913_ = l_Lean_warningAsError;
v___x_914_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_912_, v___x_913_);
lean_dec_ref(v___x_912_);
if (v___x_914_ == 0)
{
v___y_896_ = v___y_909_;
v___y_897_ = v_severity_814_;
goto v___jp_895_;
}
else
{
v___y_896_ = v___y_909_;
v___y_897_ = v___x_907_;
goto v___jp_895_;
}
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
lean_object* v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v_env_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1534_ = lean_st_ref_get(v_a_1532_);
v_env_1541_ = lean_ctor_get(v___x_1534_, 0);
lean_inc_ref(v_env_1541_);
lean_dec(v___x_1534_);
v___x_1542_ = l_Lean_getMainVersoModuleDocs(v_env_1541_);
v___x_1543_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1542_);
lean_dec_ref(v___x_1542_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1526_);
v___x_1545_ = lean_unsigned_to_nat(0u);
v___y_1536_ = v___x_1544_;
v___y_1537_ = v___x_1545_;
goto v___jp_1535_;
}
else
{
lean_object* v_val_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_val_1546_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_val_1546_, v___x_1547_);
lean_dec(v_val_1546_);
v___x_1549_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1526_);
v___y_1536_ = v___x_1549_;
v___y_1537_ = v___x_1548_;
goto v___jp_1535_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1550_, lean_object* v_doc_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_versoModDocString(v_range_1550_, v_doc_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_doc_1551_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1569_, lean_object* v_docComment_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1579_ = l_Lean_versoDocStringOfText(v_declName_1569_, v___x_1578_, v_docComment_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1580_, lean_object* v_docComment_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_versoDocStringFromString(v_declName_1580_, v_docComment_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1590_, lean_object* v_declName_1591_, uint8_t v___x_1592_, lean_object* v_env_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = l_Lean_docStringExt;
v___x_1595_ = l_String_removeLeadingSpaces(v_docString_1590_);
v___x_1596_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1594_, v_env_1593_, v_declName_1591_, v___x_1595_, v___x_1592_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0___boxed(lean_object* v_docString_1597_, lean_object* v_declName_1598_, lean_object* v___x_1599_, lean_object* v_env_1600_){
_start:
{
uint8_t v___x_198__boxed_1601_; lean_object* v_res_1602_; 
v___x_198__boxed_1601_ = lean_unbox(v___x_1599_);
v_res_1602_ = l_Lean_addMarkdownDocString___redArg___lam__0(v_docString_1597_, v_declName_1598_, v___x_198__boxed_1601_, v_env_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1603_, uint8_t v___x_1604_, lean_object* v_modifyEnv_1605_, lean_object* v_docString_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_box(v___x_1604_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1608_, 0, v_docString_1606_);
lean_closure_set(v___f_1608_, 1, v_declName_1603_);
lean_closure_set(v___f_1608_, 2, v___x_1607_);
v___x_1609_ = lean_apply_1(v_modifyEnv_1605_, v___f_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1___boxed(lean_object* v_declName_1610_, lean_object* v___x_1611_, lean_object* v_modifyEnv_1612_, lean_object* v_docString_1613_){
_start:
{
uint8_t v___x_207__boxed_1614_; lean_object* v_res_1615_; 
v___x_207__boxed_1614_ = lean_unbox(v___x_1611_);
v_res_1615_ = l_Lean_addMarkdownDocString___redArg___lam__1(v_declName_1610_, v___x_207__boxed_1614_, v_modifyEnv_1612_, v_docString_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_docComment_1618_, lean_object* v_toBind_1619_, lean_object* v___f_1620_, lean_object* v_____r_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_Lean_getDocStringText___redArg(v_inst_1616_, v_inst_1617_, v_docComment_1618_);
v___x_1623_ = lean_apply_4(v_toBind_1619_, lean_box(0), lean_box(0), v___x_1622_, v___f_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_docComment_1629_, lean_object* v_toBind_1630_, lean_object* v___f_1631_, lean_object* v_____r_1632_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Lean_validateDocComment___redArg(v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_inst_1628_, v_docComment_1629_);
v___x_1634_ = lean_apply_4(v_toBind_1630_, lean_box(0), lean_box(0), v___x_1633_, v___f_1631_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_docComment_1640_, lean_object* v_toBind_1641_, lean_object* v___f_1642_, lean_object* v_____r_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1635_, v_inst_1636_, v_inst_1637_, v_inst_1638_, v_inst_1639_, v_docComment_1640_, v_toBind_1641_, v___f_1642_, v_____r_1643_);
lean_dec(v_docComment_1640_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1645_, lean_object* v_____r_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_apply_1(v___f_1645_, v_____r_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1653_ = l_Lean_stringToMessageData(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v_declName_1654_, lean_object* v___f_1655_, uint8_t v___x_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_toBind_1659_, lean_object* v___f_1660_, lean_object* v_____do__lift_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1661_, v_declName_1654_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v___f_1660_);
lean_dec(v_toBind_1659_);
lean_dec_ref(v_inst_1658_);
lean_dec_ref(v_inst_1657_);
lean_dec(v_declName_1654_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_apply_1(v___f_1655_, v___x_1663_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref_known(v___x_1662_, 1);
lean_dec(v___f_1655_);
v___x_1665_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1666_ = l_Lean_MessageData_ofConstName(v_declName_1654_, v___x_1656_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_throwError___redArg(v_inst_1657_, v_inst_1658_, v___x_1669_);
v___x_1671_ = lean_apply_4(v_toBind_1659_, lean_box(0), lean_box(0), v___x_1670_, v___f_1660_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v_declName_1672_, lean_object* v___f_1673_, lean_object* v___x_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_toBind_1677_, lean_object* v___f_1678_, lean_object* v_____do__lift_1679_){
_start:
{
uint8_t v___x_272__boxed_1680_; lean_object* v_res_1681_; 
v___x_272__boxed_1680_ = lean_unbox(v___x_1674_);
v_res_1681_ = l_Lean_addMarkdownDocString___redArg___lam__5(v_declName_1672_, v___f_1673_, v___x_272__boxed_1680_, v_inst_1675_, v_inst_1676_, v_toBind_1677_, v___f_1678_, v_____do__lift_1679_);
lean_dec_ref(v_____do__lift_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_declName_1689_, lean_object* v_docComment_1690_){
_start:
{
lean_object* v_toApplicative_1691_; lean_object* v_toBind_1692_; lean_object* v_toPure_1693_; uint8_t v___x_1694_; 
v_toApplicative_1691_ = lean_ctor_get(v_inst_1682_, 0);
v_toBind_1692_ = lean_ctor_get(v_inst_1682_, 1);
lean_inc(v_toBind_1692_);
v_toPure_1693_ = lean_ctor_get(v_toApplicative_1691_, 1);
v___x_1694_ = l_Lean_Name_isAnonymous(v_declName_1689_);
if (v___x_1694_ == 0)
{
lean_object* v_getEnv_1695_; lean_object* v_modifyEnv_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; 
v_getEnv_1695_ = lean_ctor_get(v_inst_1685_, 0);
lean_inc(v_getEnv_1695_);
v_modifyEnv_1696_ = lean_ctor_get(v_inst_1685_, 1);
lean_inc(v_modifyEnv_1696_);
lean_dec_ref(v_inst_1685_);
v___x_1697_ = 1;
v___x_1698_ = lean_box(v___x_1697_);
lean_inc(v_declName_1689_);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1699_, 0, v_declName_1689_);
lean_closure_set(v___f_1699_, 1, v___x_1698_);
lean_closure_set(v___f_1699_, 2, v_modifyEnv_1696_);
lean_inc_n(v_toBind_1692_, 3);
lean_inc(v_docComment_1690_);
lean_inc_ref(v_inst_1686_);
lean_inc_ref_n(v_inst_1682_, 2);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1700_, 0, v_inst_1682_);
lean_closure_set(v___f_1700_, 1, v_inst_1686_);
lean_closure_set(v___f_1700_, 2, v_docComment_1690_);
lean_closure_set(v___f_1700_, 3, v_toBind_1692_);
lean_closure_set(v___f_1700_, 4, v___f_1699_);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1701_, 0, v_inst_1682_);
lean_closure_set(v___f_1701_, 1, v_inst_1683_);
lean_closure_set(v___f_1701_, 2, v_inst_1687_);
lean_closure_set(v___f_1701_, 3, v_inst_1688_);
lean_closure_set(v___f_1701_, 4, v_inst_1684_);
lean_closure_set(v___f_1701_, 5, v_docComment_1690_);
lean_closure_set(v___f_1701_, 6, v_toBind_1692_);
lean_closure_set(v___f_1701_, 7, v___f_1700_);
lean_inc_ref(v___f_1701_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1702_, 0, v___f_1701_);
v___x_1703_ = lean_box(v___x_1694_);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1704_, 0, v_declName_1689_);
lean_closure_set(v___f_1704_, 1, v___f_1701_);
lean_closure_set(v___f_1704_, 2, v___x_1703_);
lean_closure_set(v___f_1704_, 3, v_inst_1682_);
lean_closure_set(v___f_1704_, 4, v_inst_1686_);
lean_closure_set(v___f_1704_, 5, v_toBind_1692_);
lean_closure_set(v___f_1704_, 6, v___f_1702_);
v___x_1705_ = lean_apply_4(v_toBind_1692_, lean_box(0), lean_box(0), v_getEnv_1695_, v___f_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_inc(v_toPure_1693_);
lean_dec(v_toBind_1692_);
lean_dec(v_docComment_1690_);
lean_dec(v_declName_1689_);
lean_dec(v_inst_1688_);
lean_dec_ref(v_inst_1687_);
lean_dec_ref(v_inst_1686_);
lean_dec_ref(v_inst_1685_);
lean_dec_ref(v_inst_1684_);
lean_dec(v_inst_1683_);
lean_dec_ref(v_inst_1682_);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_apply_2(v_toPure_1693_, lean_box(0), v___x_1706_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_declName_1716_, lean_object* v_docComment_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_addMarkdownDocString___redArg(v_inst_1709_, v_inst_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v_inst_1714_, v_inst_1715_, v_declName_1716_, v_docComment_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_addEntryFn_1719_, lean_object* v___x_1720_, lean_object* v_s_1721_){
_start:
{
lean_object* v_importedEntries_1722_; lean_object* v_state_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_importedEntries_1722_ = lean_ctor_get(v_s_1721_, 0);
v_state_1723_ = lean_ctor_get(v_s_1721_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_s_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v_s_1721_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_state_1723_);
lean_inc(v_importedEntries_1722_);
lean_dec(v_s_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_state_1727_; lean_object* v___x_1729_; 
v_state_1727_ = lean_apply_2(v_addEntryFn_1719_, v_state_1723_, v___x_1720_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_state_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_importedEntries_1722_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_state_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1732_, lean_object* v_x1_1733_, lean_object* v_x2_1734_){
_start:
{
lean_object* v_index_1735_; lean_object* v_sourceString_1736_; lean_object* v_imports_1737_; lean_object* v_currNamespace_1738_; lean_object* v_openDecls_1739_; lean_object* v_options_1740_; lean_object* v_check_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1760_; 
v_index_1735_ = lean_ctor_get(v_x2_1734_, 1);
v_sourceString_1736_ = lean_ctor_get(v_x2_1734_, 2);
v_imports_1737_ = lean_ctor_get(v_x2_1734_, 3);
v_currNamespace_1738_ = lean_ctor_get(v_x2_1734_, 4);
v_openDecls_1739_ = lean_ctor_get(v_x2_1734_, 5);
v_options_1740_ = lean_ctor_get(v_x2_1734_, 6);
v_check_1741_ = lean_ctor_get(v_x2_1734_, 7);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_x2_1734_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_x2_1734_, 0);
lean_dec(v_unused_1761_);
v___x_1743_ = v_x2_1734_;
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_check_1741_);
lean_inc(v_options_1740_);
lean_inc(v_openDecls_1739_);
lean_inc(v_currNamespace_1738_);
lean_inc(v_imports_1737_);
lean_inc(v_sourceString_1736_);
lean_inc(v_index_1735_);
lean_dec(v_x2_1734_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v_toEnvExtension_1746_; lean_object* v_addEntryFn_1747_; lean_object* v_asyncMode_1748_; uint8_t v_logWrites_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1745_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1746_ = lean_ctor_get(v___x_1745_, 0);
v_addEntryFn_1747_ = lean_ctor_get(v___x_1745_, 3);
v_asyncMode_1748_ = lean_ctor_get(v_toEnvExtension_1746_, 2);
v_logWrites_1749_ = lean_ctor_get_uint8(v_toEnvExtension_1746_, sizeof(void*)*6);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_declName_1732_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1750_);
v___x_1752_ = v___x_1743_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_index_1735_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_sourceString_1736_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_imports_1737_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_currNamespace_1738_);
lean_ctor_set(v_reuseFailAlloc_1759_, 5, v_openDecls_1739_);
lean_ctor_set(v_reuseFailAlloc_1759_, 6, v_options_1740_);
lean_ctor_set(v_reuseFailAlloc_1759_, 7, v_check_1741_);
v___x_1752_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___f_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
lean_inc(v_addEntryFn_1747_);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1753_, 0, v_addEntryFn_1747_);
lean_closure_set(v___f_1753_, 1, v___x_1752_);
v___x_1754_ = lean_box(0);
v___x_1755_ = 1;
if (v_logWrites_1749_ == 0)
{
lean_object* v___x_1756_; 
lean_inc_ref(v_toEnvExtension_1746_);
v___x_1756_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1746_, v_x1_1733_, v___f_1753_, v_asyncMode_1748_, v___x_1754_, v___x_1755_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_inc_ref_n(v_toEnvExtension_1746_, 2);
v___x_1757_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1746_, v_x1_1733_);
lean_dec_ref(v_x1_1733_);
v___x_1758_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1746_, v___x_1757_, v___f_1753_, v_asyncMode_1748_, v___x_1754_, v___x_1755_);
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_1781_, lean_object* v_docs_1782_, uint8_t v___x_1783_, lean_object* v_deferred_1784_, lean_object* v___f_1785_, lean_object* v_env_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1787_ = l_Lean_versoDocStringExt;
v_env_1788_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1787_, v_env_1786_, v_declName_1781_, v_docs_1782_, v___x_1783_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_array_get_size(v_deferred_1784_);
v___x_1791_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1792_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
if (v___x_1792_ == 0)
{
lean_dec_ref(v___f_1785_);
lean_dec_ref(v_deferred_1784_);
return v_env_1788_;
}
else
{
size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = lean_usize_of_nat(v___x_1790_);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1791_, v___f_1785_, v_deferred_1784_, v___x_1793_, v___x_1794_, v_env_1788_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1796_, lean_object* v_docs_1797_, lean_object* v___x_1798_, lean_object* v_deferred_1799_, lean_object* v___f_1800_, lean_object* v_env_1801_){
_start:
{
uint8_t v___x_385__boxed_1802_; lean_object* v_res_1803_; 
v___x_385__boxed_1802_ = lean_unbox(v___x_1798_);
v_res_1803_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_1796_, v_docs_1797_, v___x_385__boxed_1802_, v_deferred_1799_, v___f_1800_, v_env_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_modifyEnv_1804_, lean_object* v___f_1805_, lean_object* v_____r_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_apply_1(v_modifyEnv_1804_, v___f_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object* v_declName_1810_, lean_object* v_modifyEnv_1811_, lean_object* v___f_1812_, uint8_t v___x_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_toBind_1816_, lean_object* v___f_1817_, lean_object* v_____do__lift_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1818_, v_declName_1810_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1820_; 
lean_dec(v___f_1817_);
lean_dec(v_toBind_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec(v_declName_1810_);
v___x_1820_ = lean_apply_1(v_modifyEnv_1811_, v___f_1812_);
return v___x_1820_;
}
else
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1835_; 
lean_dec_ref(v___f_1812_);
lean_dec(v_modifyEnv_1811_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1836_);
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1835_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1835_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1824_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_1825_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1810_, v___x_1813_);
v___x_1826_ = lean_string_append(v___x_1824_, v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_1828_ = lean_string_append(v___x_1826_, v___x_1827_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 3);
lean_ctor_set(v___x_1822_, 0, v___x_1828_);
v___x_1830_ = v___x_1822_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = l_Lean_MessageData_ofFormat(v___x_1830_);
v___x_1832_ = l_Lean_throwError___redArg(v_inst_1814_, v_inst_1815_, v___x_1831_);
v___x_1833_ = lean_apply_4(v_toBind_1816_, lean_box(0), lean_box(0), v___x_1832_, v___f_1817_);
return v___x_1833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object* v_declName_1837_, lean_object* v_modifyEnv_1838_, lean_object* v___f_1839_, lean_object* v___x_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_toBind_1843_, lean_object* v___f_1844_, lean_object* v_____do__lift_1845_){
_start:
{
uint8_t v___x_437__boxed_1846_; lean_object* v_res_1847_; 
v___x_437__boxed_1846_ = lean_unbox(v___x_1840_);
v_res_1847_ = l_Lean_addVersoDocStringCore___redArg___lam__4(v_declName_1837_, v_modifyEnv_1838_, v___f_1839_, v___x_437__boxed_1846_, v_inst_1841_, v_inst_1842_, v_toBind_1843_, v___f_1844_, v_____do__lift_1845_);
lean_dec_ref(v_____do__lift_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_declName_1851_, lean_object* v_docs_1852_, lean_object* v_deferred_1853_){
_start:
{
lean_object* v_toApplicative_1854_; lean_object* v_toBind_1855_; lean_object* v_toPure_1856_; uint8_t v___x_1857_; 
v_toApplicative_1854_ = lean_ctor_get(v_inst_1848_, 0);
v_toBind_1855_ = lean_ctor_get(v_inst_1848_, 1);
lean_inc(v_toBind_1855_);
v_toPure_1856_ = lean_ctor_get(v_toApplicative_1854_, 1);
v___x_1857_ = l_Lean_Name_isAnonymous(v_declName_1851_);
if (v___x_1857_ == 0)
{
lean_object* v_getEnv_1858_; lean_object* v_modifyEnv_1859_; lean_object* v___f_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; lean_object* v___f_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___f_1866_; lean_object* v___x_1867_; 
v_getEnv_1858_ = lean_ctor_get(v_inst_1849_, 0);
lean_inc(v_getEnv_1858_);
v_modifyEnv_1859_ = lean_ctor_get(v_inst_1849_, 1);
lean_inc_n(v_modifyEnv_1859_, 2);
lean_dec_ref(v_inst_1849_);
lean_inc_n(v_declName_1851_, 2);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1860_, 0, v_declName_1851_);
v___x_1861_ = 1;
v___x_1862_ = lean_box(v___x_1861_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1863_, 0, v_declName_1851_);
lean_closure_set(v___f_1863_, 1, v_docs_1852_);
lean_closure_set(v___f_1863_, 2, v___x_1862_);
lean_closure_set(v___f_1863_, 3, v_deferred_1853_);
lean_closure_set(v___f_1863_, 4, v___f_1860_);
lean_inc_ref(v___f_1863_);
v___f_1864_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3), 3, 2);
lean_closure_set(v___f_1864_, 0, v_modifyEnv_1859_);
lean_closure_set(v___f_1864_, 1, v___f_1863_);
v___x_1865_ = lean_box(v___x_1861_);
lean_inc(v_toBind_1855_);
v___f_1866_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_1866_, 0, v_declName_1851_);
lean_closure_set(v___f_1866_, 1, v_modifyEnv_1859_);
lean_closure_set(v___f_1866_, 2, v___f_1863_);
lean_closure_set(v___f_1866_, 3, v___x_1865_);
lean_closure_set(v___f_1866_, 4, v_inst_1848_);
lean_closure_set(v___f_1866_, 5, v_inst_1850_);
lean_closure_set(v___f_1866_, 6, v_toBind_1855_);
lean_closure_set(v___f_1866_, 7, v___f_1864_);
v___x_1867_ = lean_apply_4(v_toBind_1855_, lean_box(0), lean_box(0), v_getEnv_1858_, v___f_1866_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_inc(v_toPure_1856_);
lean_dec(v_toBind_1855_);
lean_dec_ref(v_deferred_1853_);
lean_dec_ref(v_docs_1852_);
lean_dec(v_declName_1851_);
lean_dec_ref(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
lean_dec_ref(v_inst_1848_);
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_apply_2(v_toPure_1856_, lean_box(0), v___x_1868_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_declName_1875_, lean_object* v_docs_1876_, lean_object* v_deferred_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1871_, v_inst_1872_, v_inst_1874_, v_declName_1875_, v_docs_1876_, v_deferred_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_declName_1884_, lean_object* v_docs_1885_, lean_object* v_deferred_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_addVersoDocStringCore(v_m_1879_, v_inst_1880_, v_inst_1881_, v_inst_1882_, v_inst_1883_, v_declName_1884_, v_docs_1885_, v_deferred_1886_);
lean_dec(v_inst_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_size_1888_, uint8_t v___x_1889_, lean_object* v_x1_1890_, lean_object* v_x2_1891_){
_start:
{
lean_object* v_index_1892_; lean_object* v_sourceString_1893_; lean_object* v_imports_1894_; lean_object* v_currNamespace_1895_; lean_object* v_openDecls_1896_; lean_object* v_options_1897_; lean_object* v_check_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1916_; 
v_index_1892_ = lean_ctor_get(v_x2_1891_, 1);
v_sourceString_1893_ = lean_ctor_get(v_x2_1891_, 2);
v_imports_1894_ = lean_ctor_get(v_x2_1891_, 3);
v_currNamespace_1895_ = lean_ctor_get(v_x2_1891_, 4);
v_openDecls_1896_ = lean_ctor_get(v_x2_1891_, 5);
v_options_1897_ = lean_ctor_get(v_x2_1891_, 6);
v_check_1898_ = lean_ctor_get(v_x2_1891_, 7);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_x2_1891_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v_x2_1891_, 0);
lean_dec(v_unused_1917_);
v___x_1900_ = v_x2_1891_;
v_isShared_1901_ = v_isSharedCheck_1916_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_check_1898_);
lean_inc(v_options_1897_);
lean_inc(v_openDecls_1896_);
lean_inc(v_currNamespace_1895_);
lean_inc(v_imports_1894_);
lean_inc(v_sourceString_1893_);
lean_inc(v_index_1892_);
lean_dec(v_x2_1891_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1916_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v_toEnvExtension_1903_; lean_object* v_addEntryFn_1904_; lean_object* v_asyncMode_1905_; uint8_t v_logWrites_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1902_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1903_ = lean_ctor_get(v___x_1902_, 0);
v_addEntryFn_1904_ = lean_ctor_get(v___x_1902_, 3);
v_asyncMode_1905_ = lean_ctor_get(v_toEnvExtension_1903_, 2);
v_logWrites_1906_ = lean_ctor_get_uint8(v_toEnvExtension_1903_, sizeof(void*)*6);
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_size_1888_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1907_);
v___x_1909_ = v___x_1900_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_index_1892_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_sourceString_1893_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_imports_1894_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_currNamespace_1895_);
lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_openDecls_1896_);
lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_options_1897_);
lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_check_1898_);
v___x_1909_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___f_1910_; lean_object* v___x_1911_; 
lean_inc(v_addEntryFn_1904_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1910_, 0, v_addEntryFn_1904_);
lean_closure_set(v___f_1910_, 1, v___x_1909_);
v___x_1911_ = lean_box(0);
if (v_logWrites_1906_ == 0)
{
lean_object* v___x_1912_; 
lean_inc_ref(v_toEnvExtension_1903_);
v___x_1912_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1903_, v_x1_1890_, v___f_1910_, v_asyncMode_1905_, v___x_1911_, v___x_1889_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_inc_ref_n(v_toEnvExtension_1903_, 2);
v___x_1913_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1903_, v_x1_1890_);
lean_dec_ref(v_x1_1890_);
v___x_1914_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1903_, v___x_1913_, v___f_1910_, v_asyncMode_1905_, v___x_1911_, v___x_1889_);
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed(lean_object* v_size_1918_, lean_object* v___x_1919_, lean_object* v_x1_1920_, lean_object* v_x2_1921_){
_start:
{
uint8_t v___x_305__boxed_1922_; lean_object* v_res_1923_; 
v___x_305__boxed_1922_ = lean_unbox(v___x_1919_);
v_res_1923_ = l_Lean_addVersoModDocStringCore___redArg___lam__1(v_size_1918_, v___x_305__boxed_1922_, v_x1_1920_, v_x2_1921_);
return v_res_1923_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_1926_ = l_Lean_stringToMessageData(v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_deferred_1930_, lean_object* v_inst_1931_, lean_object* v___f_1932_, lean_object* v_____do__lift_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1933_, v_docs_1927_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec_ref(v___f_1932_);
lean_dec_ref(v_inst_1931_);
lean_dec_ref(v_deferred_1930_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_1937_ = l_Lean_stringToMessageData(v_a_1935_);
v___x_1938_ = l_Lean_indentD(v___x_1937_);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1936_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_throwError___redArg(v_inst_1928_, v_inst_1929_, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
lean_dec_ref(v_inst_1929_);
lean_dec_ref(v_inst_1928_);
v_a_1941_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_array_get_size(v_deferred_1930_);
v___x_1944_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1945_ = lean_nat_dec_lt(v___x_1942_, v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_dec_ref(v___f_1932_);
lean_dec_ref(v_deferred_1930_);
v___x_1946_ = l_Lean_setEnv___redArg(v_inst_1931_, v_a_1941_);
return v___x_1946_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1943_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1944_, v___f_1932_, v_deferred_1930_, v___x_1947_, v___x_1948_, v_a_1941_);
v___x_1950_ = l_Lean_setEnv___redArg(v_inst_1931_, v___x_1949_);
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(uint8_t v___x_1951_, lean_object* v_docs_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_deferred_1955_, lean_object* v_inst_1956_, lean_object* v_toBind_1957_, lean_object* v_getEnv_1958_, lean_object* v_____do__lift_1959_){
_start:
{
lean_object* v___x_1960_; lean_object* v_size_1961_; lean_object* v___x_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; 
v___x_1960_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_1959_);
v_size_1961_ = lean_ctor_get(v___x_1960_, 2);
lean_inc(v_size_1961_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = lean_box(v___x_1951_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1963_, 0, v_size_1961_);
lean_closure_set(v___f_1963_, 1, v___x_1962_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1964_, 0, v_docs_1952_);
lean_closure_set(v___f_1964_, 1, v_inst_1953_);
lean_closure_set(v___f_1964_, 2, v_inst_1954_);
lean_closure_set(v___f_1964_, 3, v_deferred_1955_);
lean_closure_set(v___f_1964_, 4, v_inst_1956_);
lean_closure_set(v___f_1964_, 5, v___f_1963_);
v___x_1965_ = lean_apply_4(v_toBind_1957_, lean_box(0), lean_box(0), v_getEnv_1958_, v___f_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed(lean_object* v___x_1966_, lean_object* v_docs_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_deferred_1970_, lean_object* v_inst_1971_, lean_object* v_toBind_1972_, lean_object* v_getEnv_1973_, lean_object* v_____do__lift_1974_){
_start:
{
uint8_t v___x_416__boxed_1975_; lean_object* v_res_1976_; 
v___x_416__boxed_1975_ = lean_unbox(v___x_1966_);
v_res_1976_ = l_Lean_addVersoModDocStringCore___redArg___lam__2(v___x_416__boxed_1975_, v_docs_1967_, v_inst_1968_, v_inst_1969_, v_deferred_1970_, v_inst_1971_, v_toBind_1972_, v_getEnv_1973_, v_____do__lift_1974_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v_docs_1982_, lean_object* v_deferred_1983_, lean_object* v_inst_1984_, lean_object* v_toBind_1985_, lean_object* v_getEnv_1986_, lean_object* v_____do__lift_1987_){
_start:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = l_Lean_getMainModuleDoc(v_____do__lift_1987_);
v___x_1989_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_1988_);
lean_dec_ref(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_getEnv_1986_);
lean_dec(v_toBind_1985_);
lean_dec_ref(v_inst_1984_);
lean_dec_ref(v_deferred_1983_);
lean_dec_ref(v_docs_1982_);
v___x_1990_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_1991_ = l_Lean_throwError___redArg(v_inst_1980_, v_inst_1981_, v___x_1990_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_box(v___x_1989_);
lean_inc(v_getEnv_1986_);
lean_inc(v_toBind_1985_);
v___f_1993_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1993_, 0, v___x_1992_);
lean_closure_set(v___f_1993_, 1, v_docs_1982_);
lean_closure_set(v___f_1993_, 2, v_inst_1980_);
lean_closure_set(v___f_1993_, 3, v_inst_1981_);
lean_closure_set(v___f_1993_, 4, v_deferred_1983_);
lean_closure_set(v___f_1993_, 5, v_inst_1984_);
lean_closure_set(v___f_1993_, 6, v_toBind_1985_);
lean_closure_set(v___f_1993_, 7, v_getEnv_1986_);
v___x_1994_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v_getEnv_1986_, v___f_1993_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_1995_, lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_docs_1998_, lean_object* v_deferred_1999_){
_start:
{
lean_object* v_toBind_2000_; lean_object* v_getEnv_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; 
v_toBind_2000_ = lean_ctor_get(v_inst_1995_, 1);
lean_inc_n(v_toBind_2000_, 2);
v_getEnv_2001_ = lean_ctor_get(v_inst_1996_, 0);
lean_inc_n(v_getEnv_2001_, 2);
v___f_2002_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2002_, 0, v_inst_1995_);
lean_closure_set(v___f_2002_, 1, v_inst_1997_);
lean_closure_set(v___f_2002_, 2, v_docs_1998_);
lean_closure_set(v___f_2002_, 3, v_deferred_1999_);
lean_closure_set(v___f_2002_, 4, v_inst_1996_);
lean_closure_set(v___f_2002_, 5, v_toBind_2000_);
lean_closure_set(v___f_2002_, 6, v_getEnv_2001_);
v___x_2003_ = lean_apply_4(v_toBind_2000_, lean_box(0), lean_box(0), v_getEnv_2001_, v___f_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_docs_2009_, lean_object* v_deferred_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2005_, v_inst_2006_, v_inst_2008_, v_docs_2009_, v_deferred_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_docs_2017_, lean_object* v_deferred_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_addVersoModDocStringCore(v_m_2012_, v_inst_2013_, v_inst_2014_, v_inst_2015_, v_inst_2016_, v_docs_2017_, v_deferred_2018_);
lean_dec(v_inst_2015_);
return v_res_2019_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(1);
v___x_2021_ = l_Lean_MessageData_ofFormat(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__2));
v___x_2026_ = l_Lean_MessageData_ofFormat(v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5(lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
return v_x_2027_;
}
else
{
lean_object* v_head_2029_; lean_object* v_tail_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2052_; 
v_head_2029_ = lean_ctor_get(v_x_2028_, 0);
v_tail_2030_ = lean_ctor_get(v_x_2028_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2032_ = v_x_2028_;
v_isShared_2033_ = v_isSharedCheck_2052_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_tail_2030_);
lean_inc(v_head_2029_);
lean_dec(v_x_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2052_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_before_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2050_; 
v_before_2034_ = lean_ctor_get(v_head_2029_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_head_2029_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_head_2029_, 1);
lean_dec(v_unused_2051_);
v___x_2036_ = v_head_2029_;
v_isShared_2037_ = v_isSharedCheck_2050_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_before_2034_);
lean_dec(v_head_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2050_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 7);
lean_ctor_set(v___x_2036_, 1, v___x_2038_);
lean_ctor_set(v___x_2036_, 0, v_x_2027_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_x_2027_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3);
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 7);
lean_ctor_set(v___x_2032_, 1, v___x_2041_);
lean_ctor_set(v___x_2032_, 0, v___x_2040_);
v___x_2043_ = v___x_2032_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = l_Lean_MessageData_ofSyntax(v_before_2034_);
v___x_2045_ = l_Lean_indentD(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2043_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v_x_2027_ = v___x_2046_;
v_x_2028_ = v_tail_2030_;
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
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__1));
v___x_2057_ = l_Lean_MessageData_ofFormat(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(lean_object* v_msgData_2058_, lean_object* v_macroStack_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2060_);
v___x_2063_ = l_Lean_Elab_pp_macroStack;
v___x_2064_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_2062_, v___x_2063_);
lean_dec_ref(v___x_2062_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec(v_macroStack_2059_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_msgData_2058_);
return v___x_2065_;
}
else
{
if (lean_obj_tag(v_macroStack_2059_) == 0)
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_msgData_2058_);
return v___x_2066_;
}
else
{
lean_object* v_head_2067_; lean_object* v_after_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2083_; 
v_head_2067_ = lean_ctor_get(v_macroStack_2059_, 0);
lean_inc(v_head_2067_);
v_after_2068_ = lean_ctor_get(v_head_2067_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_head_2067_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_head_2067_, 0);
lean_dec(v_unused_2084_);
v___x_2070_ = v_head_2067_;
v_isShared_2071_ = v_isSharedCheck_2083_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_after_2068_);
lean_dec(v_head_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2083_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 7);
lean_ctor_set(v___x_2070_, 1, v___x_2072_);
lean_ctor_set(v___x_2070_, 0, v_msgData_2058_);
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_msgData_2058_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_msgData_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2075_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l_Lean_MessageData_ofSyntax(v_after_2068_);
v___x_2078_ = l_Lean_indentD(v___x_2077_);
v_msgData_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2079_, 0, v___x_2076_);
lean_ctor_set(v_msgData_2079_, 1, v___x_2078_);
v___x_2080_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5(v_msgData_2079_, v_macroStack_2059_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_2085_, lean_object* v_macroStack_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(v_msgData_2085_, v_macroStack_2086_, v___y_2087_);
lean_dec_ref(v___y_2087_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_ref_2098_; lean_object* v_macroStack_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2112_; 
v_ref_2098_ = lean_ctor_get(v___y_2095_, 2);
v_macroStack_2099_ = lean_ctor_get(v___y_2091_, 1);
v___x_2100_ = l_Lean_Elab_getBetterRef(v_ref_2098_, v_macroStack_2099_);
v___x_2101_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2090_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
lean_inc(v_macroStack_2099_);
v___x_2103_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(v_a_2102_, v_macroStack_2099_, v___y_2095_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2100_);
lean_ctor_set(v___x_2108_, 1, v_a_2104_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 1);
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2121_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg();
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0(lean_object* v_addEntryFn_2128_, lean_object* v___x_2129_, lean_object* v_s_2130_){
_start:
{
lean_object* v_importedEntries_2131_; lean_object* v_state_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2140_; 
v_importedEntries_2131_ = lean_ctor_get(v_s_2130_, 0);
v_state_2132_ = lean_ctor_get(v_s_2130_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_s_2130_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2134_ = v_s_2130_;
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_state_2132_);
lean_inc(v_importedEntries_2131_);
lean_dec(v_s_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_state_2136_; lean_object* v___x_2138_; 
v_state_2136_ = lean_apply_2(v_addEntryFn_2128_, v_state_2132_, v___x_2129_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 1, v_state_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_importedEntries_2131_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_state_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(lean_object* v_declName_2141_, lean_object* v_as_2142_, size_t v_i_2143_, size_t v_stop_2144_, lean_object* v_b_2145_){
_start:
{
lean_object* v___y_2147_; uint8_t v___x_2151_; 
v___x_2151_ = lean_usize_dec_eq(v_i_2143_, v_stop_2144_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v_index_2153_; lean_object* v_sourceString_2154_; lean_object* v_imports_2155_; lean_object* v_currNamespace_2156_; lean_object* v_openDecls_2157_; lean_object* v_options_2158_; lean_object* v_check_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2178_; 
v___x_2152_ = lean_array_uget(v_as_2142_, v_i_2143_);
v_index_2153_ = lean_ctor_get(v___x_2152_, 1);
v_sourceString_2154_ = lean_ctor_get(v___x_2152_, 2);
v_imports_2155_ = lean_ctor_get(v___x_2152_, 3);
v_currNamespace_2156_ = lean_ctor_get(v___x_2152_, 4);
v_openDecls_2157_ = lean_ctor_get(v___x_2152_, 5);
v_options_2158_ = lean_ctor_get(v___x_2152_, 6);
v_check_2159_ = lean_ctor_get(v___x_2152_, 7);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v___x_2152_, 0);
lean_dec(v_unused_2179_);
v___x_2161_ = v___x_2152_;
v_isShared_2162_ = v_isSharedCheck_2178_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_check_2159_);
lean_inc(v_options_2158_);
lean_inc(v_openDecls_2157_);
lean_inc(v_currNamespace_2156_);
lean_inc(v_imports_2155_);
lean_inc(v_sourceString_2154_);
lean_inc(v_index_2153_);
lean_dec(v___x_2152_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2178_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v_toEnvExtension_2164_; lean_object* v_addEntryFn_2165_; lean_object* v_asyncMode_2166_; uint8_t v_logWrites_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2163_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2164_ = lean_ctor_get(v___x_2163_, 0);
v_addEntryFn_2165_ = lean_ctor_get(v___x_2163_, 3);
v_asyncMode_2166_ = lean_ctor_get(v_toEnvExtension_2164_, 2);
v_logWrites_2167_ = lean_ctor_get_uint8(v_toEnvExtension_2164_, sizeof(void*)*6);
lean_inc(v_declName_2141_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_declName_2141_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2168_);
v___x_2170_ = v___x_2161_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_index_2153_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_sourceString_2154_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_imports_2155_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_currNamespace_2156_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v_openDecls_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v_options_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v_check_2159_);
v___x_2170_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
lean_inc(v_addEntryFn_2165_);
v___f_2171_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_2171_, 0, v_addEntryFn_2165_);
lean_closure_set(v___f_2171_, 1, v___x_2170_);
v___x_2172_ = lean_box(0);
v___x_2173_ = 1;
if (v_logWrites_2167_ == 0)
{
lean_object* v___x_2174_; 
lean_inc_ref(v_toEnvExtension_2164_);
v___x_2174_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2164_, v_b_2145_, v___f_2171_, v_asyncMode_2166_, v___x_2172_, v___x_2173_);
v___y_2147_ = v___x_2174_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_inc_ref_n(v_toEnvExtension_2164_, 2);
v___x_2175_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2164_, v_b_2145_);
lean_dec_ref(v_b_2145_);
v___x_2176_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2164_, v___x_2175_, v___f_2171_, v_asyncMode_2166_, v___x_2172_, v___x_2173_);
v___y_2147_ = v___x_2176_;
goto v___jp_2146_;
}
}
}
}
else
{
lean_dec(v_declName_2141_);
return v_b_2145_;
}
v___jp_2146_:
{
size_t v___x_2148_; size_t v___x_2149_; 
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2143_, v___x_2148_);
v_i_2143_ = v___x_2149_;
v_b_2145_ = v___y_2147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___boxed(lean_object* v_declName_2180_, lean_object* v_as_2181_, lean_object* v_i_2182_, lean_object* v_stop_2183_, lean_object* v_b_2184_){
_start:
{
size_t v_i_boxed_2185_; size_t v_stop_boxed_2186_; lean_object* v_res_2187_; 
v_i_boxed_2185_ = lean_unbox_usize(v_i_2182_);
lean_dec(v_i_2182_);
v_stop_boxed_2186_ = lean_unbox_usize(v_stop_2183_);
lean_dec(v_stop_2183_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(v_declName_2180_, v_as_2181_, v_i_boxed_2185_, v_stop_boxed_2186_, v_b_2184_);
lean_dec_ref(v_as_2181_);
return v_res_2187_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg();
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2194_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2195_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v___x_2193_);
lean_ctor_set(v___x_2195_, 2, v___x_2193_);
lean_ctor_set(v___x_2195_, 3, v___x_2193_);
lean_ctor_set(v___x_2195_, 4, v___x_2193_);
lean_ctor_set(v___x_2195_, 5, v___x_2193_);
lean_ctor_set(v___x_2195_, 6, v___x_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2196_, lean_object* v_docs_2197_, lean_object* v_deferred_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; uint8_t v___x_2238_; 
v___x_2238_ = l_Lean_Name_isAnonymous(v_declName_2196_);
if (v___x_2238_ == 0)
{
uint8_t v___x_2239_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___x_2261_; lean_object* v_env_2262_; lean_object* v___x_2263_; 
v___x_2239_ = 1;
v___x_2261_ = lean_st_ref_get(v___y_2204_);
v_env_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_ref(v_env_2262_);
lean_dec(v___x_2261_);
v___x_2263_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2262_, v_declName_2196_);
lean_dec_ref(v_env_2262_);
if (lean_obj_tag(v___x_2263_) == 0)
{
v___y_2241_ = v___y_2202_;
v___y_2242_ = v___y_2204_;
goto v___jp_2240_;
}
else
{
lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_docs_2197_);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v___x_2263_, 0);
lean_dec(v_unused_2278_);
v___x_2265_ = v___x_2263_;
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
else
{
lean_dec(v___x_2263_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2267_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2268_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2196_, v___x_2239_);
v___x_2269_ = lean_string_append(v___x_2267_, v___x_2268_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2271_ = lean_string_append(v___x_2269_, v___x_2270_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 3);
lean_ctor_set(v___x_2265_, 0, v___x_2271_);
v___x_2273_ = v___x_2265_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = l_Lean_MessageData_ofFormat(v___x_2273_);
v___x_2275_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2274_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v___x_2275_;
}
}
}
v___jp_2240_:
{
lean_object* v___x_2243_; lean_object* v_env_2244_; lean_object* v_nextMacroScope_2245_; lean_object* v_ngen_2246_; lean_object* v_auxDeclNGen_2247_; lean_object* v_traceState_2248_; lean_object* v_recordedDeps_2249_; lean_object* v_messages_2250_; lean_object* v_infoState_2251_; lean_object* v_snapshotTasks_2252_; lean_object* v___x_2253_; lean_object* v_env_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2243_ = lean_st_ref_take(v___y_2242_);
v_env_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc_ref(v_env_2244_);
v_nextMacroScope_2245_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_nextMacroScope_2245_);
v_ngen_2246_ = lean_ctor_get(v___x_2243_, 2);
lean_inc_ref(v_ngen_2246_);
v_auxDeclNGen_2247_ = lean_ctor_get(v___x_2243_, 3);
lean_inc_ref(v_auxDeclNGen_2247_);
v_traceState_2248_ = lean_ctor_get(v___x_2243_, 4);
lean_inc_ref(v_traceState_2248_);
v_recordedDeps_2249_ = lean_ctor_get(v___x_2243_, 6);
lean_inc_ref(v_recordedDeps_2249_);
v_messages_2250_ = lean_ctor_get(v___x_2243_, 7);
lean_inc_ref(v_messages_2250_);
v_infoState_2251_ = lean_ctor_get(v___x_2243_, 8);
lean_inc_ref(v_infoState_2251_);
v_snapshotTasks_2252_ = lean_ctor_get(v___x_2243_, 9);
lean_inc_ref(v_snapshotTasks_2252_);
lean_dec(v___x_2243_);
v___x_2253_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2196_);
v_env_2254_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2253_, v_env_2244_, v_declName_2196_, v_docs_2197_, v___x_2239_);
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = lean_array_get_size(v_deferred_2198_);
v___x_2257_ = lean_nat_dec_lt(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_dec(v_declName_2196_);
v___y_2207_ = v___y_2241_;
v___y_2208_ = v_snapshotTasks_2252_;
v___y_2209_ = v_traceState_2248_;
v___y_2210_ = v_infoState_2251_;
v___y_2211_ = v_ngen_2246_;
v___y_2212_ = v_nextMacroScope_2245_;
v___y_2213_ = v_recordedDeps_2249_;
v___y_2214_ = v_messages_2250_;
v___y_2215_ = v_auxDeclNGen_2247_;
v___y_2216_ = v___y_2242_;
v___y_2217_ = v_env_2254_;
goto v___jp_2206_;
}
else
{
size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = ((size_t)0ULL);
v___x_2259_ = lean_usize_of_nat(v___x_2256_);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(v_declName_2196_, v_deferred_2198_, v___x_2258_, v___x_2259_, v_env_2254_);
v___y_2207_ = v___y_2241_;
v___y_2208_ = v_snapshotTasks_2252_;
v___y_2209_ = v_traceState_2248_;
v___y_2210_ = v_infoState_2251_;
v___y_2211_ = v_ngen_2246_;
v___y_2212_ = v_nextMacroScope_2245_;
v___y_2213_ = v_recordedDeps_2249_;
v___y_2214_ = v_messages_2250_;
v___y_2215_ = v_auxDeclNGen_2247_;
v___y_2216_ = v___y_2242_;
v___y_2217_ = v___x_2260_;
goto v___jp_2206_;
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v_docs_2197_);
lean_dec(v_declName_2196_);
v___x_2279_ = lean_box(0);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
v___jp_2206_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_mctx_2222_; lean_object* v_zetaDeltaFVarIds_2223_; lean_object* v_postponed_2224_; lean_object* v_diag_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2236_; 
v___x_2218_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2219_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2219_, 0, v___y_2217_);
lean_ctor_set(v___x_2219_, 1, v___y_2212_);
lean_ctor_set(v___x_2219_, 2, v___y_2211_);
lean_ctor_set(v___x_2219_, 3, v___y_2215_);
lean_ctor_set(v___x_2219_, 4, v___y_2209_);
lean_ctor_set(v___x_2219_, 5, v___x_2218_);
lean_ctor_set(v___x_2219_, 6, v___y_2213_);
lean_ctor_set(v___x_2219_, 7, v___y_2214_);
lean_ctor_set(v___x_2219_, 8, v___y_2210_);
lean_ctor_set(v___x_2219_, 9, v___y_2208_);
v___x_2220_ = lean_st_ref_put(v___y_2216_, v___x_2219_);
v___x_2221_ = lean_st_ref_take(v___y_2207_);
v_mctx_2222_ = lean_ctor_get(v___x_2221_, 0);
v_zetaDeltaFVarIds_2223_ = lean_ctor_get(v___x_2221_, 2);
v_postponed_2224_ = lean_ctor_get(v___x_2221_, 3);
v_diag_2225_ = lean_ctor_get(v___x_2221_, 4);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2221_, 1);
lean_dec(v_unused_2237_);
v___x_2227_ = v___x_2221_;
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_diag_2225_);
lean_inc(v_postponed_2224_);
lean_inc(v_zetaDeltaFVarIds_2223_);
lean_inc(v_mctx_2222_);
lean_dec(v___x_2221_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2230_);
v___x_2232_ = v___x_2227_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_mctx_2222_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_zetaDeltaFVarIds_2223_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_postponed_2224_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_diag_2225_);
v___x_2232_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_st_ref_put(v___y_2207_, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2229_);
return v___x_2234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2281_, lean_object* v_docs_2282_, lean_object* v_deferred_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2281_, v_docs_2282_, v_deferred_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec_ref(v_deferred_2283_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2292_, lean_object* v_binders_2293_, lean_object* v_docComment_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___x_2322_; lean_object* v_env_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_st_ref_get(v_a_2300_);
v_env_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc_ref(v_env_2323_);
lean_dec(v___x_2322_);
v___x_2324_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2323_, v_declName_2292_);
lean_dec_ref(v_env_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
v___y_2303_ = v_a_2295_;
v___y_2304_ = v_a_2296_;
v___y_2305_ = v_a_2297_;
v___y_2306_ = v_a_2298_;
v___y_2307_ = v_a_2299_;
v___y_2308_ = v_a_2300_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_binders_2293_);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2324_, 0);
lean_dec(v_unused_2340_);
v___x_2326_ = v___x_2324_;
v_isShared_2327_ = v_isSharedCheck_2339_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v___x_2324_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2339_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2328_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2329_ = 1;
v___x_2330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2292_, v___x_2329_);
v___x_2331_ = lean_string_append(v___x_2328_, v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2333_ = lean_string_append(v___x_2331_, v___x_2332_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 3);
lean_ctor_set(v___x_2326_, 0, v___x_2333_);
v___x_2335_ = v___x_2326_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = l_Lean_MessageData_ofFormat(v___x_2335_);
v___x_2337_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2336_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2337_;
}
}
}
v___jp_2302_:
{
lean_object* v___x_2309_; 
lean_inc(v_declName_2292_);
v___x_2309_ = l_Lean_versoDocString(v_declName_2292_, v_binders_2293_, v_docComment_2294_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v_toVersoDocString_2311_; lean_object* v_deferredChecks_2312_; lean_object* v___x_2313_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v_toVersoDocString_2311_ = lean_ctor_get(v_a_2310_, 0);
lean_inc_ref(v_toVersoDocString_2311_);
v_deferredChecks_2312_ = lean_ctor_get(v_a_2310_, 1);
lean_inc_ref(v_deferredChecks_2312_);
lean_dec(v_a_2310_);
v___x_2313_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2292_, v_toVersoDocString_2311_, v_deferredChecks_2312_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec_ref(v_deferredChecks_2312_);
return v___x_2313_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_declName_2292_);
v_a_2314_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2309_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2309_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2341_, lean_object* v_binders_2342_, lean_object* v_docComment_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_addVersoDocString(v_declName_2341_, v_binders_2342_, v_docComment_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_docComment_2343_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2352_, lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2362_, lean_object* v_msg_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2362_, v_msg_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg();
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_00_u03b2_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3(lean_object* v_msgData_2380_, lean_object* v_macroStack_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(v_msgData_2380_, v_macroStack_2381_, v___y_2386_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___boxed(lean_object* v_msgData_2390_, lean_object* v_macroStack_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3(v_msgData_2390_, v_macroStack_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2400_, lean_object* v_docComment_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___x_2429_; lean_object* v_env_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_st_ref_get(v_a_2407_);
v_env_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_ref(v_env_2430_);
lean_dec(v___x_2429_);
v___x_2431_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2430_, v_declName_2400_);
lean_dec_ref(v_env_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
v___y_2410_ = v_a_2402_;
v___y_2411_ = v_a_2403_;
v___y_2412_ = v_a_2404_;
v___y_2413_ = v_a_2405_;
v___y_2414_ = v_a_2406_;
v___y_2415_ = v_a_2407_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v_docComment_2401_);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; 
v_unused_2447_ = lean_ctor_get(v___x_2431_, 0);
lean_dec(v_unused_2447_);
v___x_2433_ = v___x_2431_;
v_isShared_2434_ = v_isSharedCheck_2446_;
goto v_resetjp_2432_;
}
else
{
lean_dec(v___x_2431_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2446_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2435_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2436_ = 1;
v___x_2437_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2400_, v___x_2436_);
v___x_2438_ = lean_string_append(v___x_2435_, v___x_2437_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2440_ = lean_string_append(v___x_2438_, v___x_2439_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set_tag(v___x_2433_, 3);
lean_ctor_set(v___x_2433_, 0, v___x_2440_);
v___x_2442_ = v___x_2433_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = l_Lean_MessageData_ofFormat(v___x_2442_);
v___x_2444_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2443_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2444_;
}
}
}
v___jp_2409_:
{
lean_object* v___x_2416_; 
lean_inc(v_declName_2400_);
v___x_2416_ = l_Lean_versoDocStringFromString(v_declName_2400_, v_docComment_2401_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v_toVersoDocString_2418_; lean_object* v_deferredChecks_2419_; lean_object* v___x_2420_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v_toVersoDocString_2418_ = lean_ctor_get(v_a_2417_, 0);
lean_inc_ref(v_toVersoDocString_2418_);
v_deferredChecks_2419_ = lean_ctor_get(v_a_2417_, 1);
lean_inc_ref(v_deferredChecks_2419_);
lean_dec(v_a_2417_);
v___x_2420_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2400_, v_toVersoDocString_2418_, v_deferredChecks_2419_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref(v_deferredChecks_2419_);
return v___x_2420_;
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_declName_2400_);
v_a_2421_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2416_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2416_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2448_, lean_object* v_docComment_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_addVersoDocStringFromString(v_declName_2448_, v_docComment_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2458_, lean_object* v_msgData_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
uint8_t v___x_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = 2;
v___x_2466_ = 0;
v___x_2467_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2458_, v_msgData_2459_, v___x_2465_, v___x_2466_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2468_, lean_object* v_msgData_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2468_, v_msgData_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v_ref_2468_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2476_, lean_object* v_str_2477_, lean_object* v_as_2478_, size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_b_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_a_2490_; uint8_t v___x_2494_; 
v___x_2494_ = lean_usize_dec_lt(v_i_2480_, v_sz_2479_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_b_2481_);
return v___x_2495_;
}
else
{
lean_object* v_a_2496_; lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v_start_2499_; lean_object* v_stop_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2520_; 
v_a_2496_ = lean_array_uget_borrowed(v_as_2478_, v_i_2480_);
v_fst_2497_ = lean_ctor_get(v_a_2496_, 0);
lean_inc(v_fst_2497_);
v_snd_2498_ = lean_ctor_get(v_a_2496_, 1);
v_start_2499_ = lean_ctor_get(v_fst_2497_, 0);
v_stop_2500_ = lean_ctor_get(v_fst_2497_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_fst_2497_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2502_ = v_fst_2497_;
v_isShared_2503_ = v_isSharedCheck_2520_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_stop_2500_);
lean_inc(v_start_2499_);
lean_dec(v_fst_2497_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2520_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_box(0);
if (lean_obj_tag(v___y_2476_) == 1)
{
lean_object* v_val_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v_val_2505_ = lean_ctor_get(v___y_2476_, 0);
v___x_2506_ = lean_nat_add(v_val_2505_, v_start_2499_);
v___x_2507_ = lean_nat_add(v_val_2505_, v_stop_2500_);
v___x_2508_ = 0;
v___x_2509_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2509_, 0, v___x_2506_);
lean_ctor_set(v___x_2509_, 1, v___x_2507_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*2, v___x_2508_);
v___x_2510_ = lean_string_utf8_extract(v_str_2477_, v_start_2499_, v_stop_2500_);
lean_dec(v_stop_2500_);
lean_dec(v_start_2499_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 2);
lean_ctor_set(v___x_2502_, 1, v___x_2510_);
lean_ctor_set(v___x_2502_, 0, v___x_2509_);
v___x_2512_ = v___x_2502_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_inc(v_snd_2498_);
v___x_2513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_snd_2498_);
v___x_2514_ = l_Lean_MessageData_ofFormat(v___x_2513_);
v___x_2515_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2512_, v___x_2514_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec_ref(v___x_2512_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref_known(v___x_2515_, 1);
v_a_2490_ = v___x_2504_;
goto v___jp_2489_;
}
else
{
return v___x_2515_;
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_del_object(v___x_2502_);
lean_dec(v_stop_2500_);
lean_dec(v_start_2499_);
lean_inc(v_snd_2498_);
v___x_2517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_snd_2498_);
v___x_2518_ = l_Lean_MessageData_ofFormat(v___x_2517_);
v___x_2519_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2518_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_dec_ref_known(v___x_2519_, 1);
v_a_2490_ = v___x_2504_;
goto v___jp_2489_;
}
else
{
return v___x_2519_;
}
}
}
}
v___jp_2489_:
{
size_t v___x_2491_; size_t v___x_2492_; 
v___x_2491_ = ((size_t)1ULL);
v___x_2492_ = lean_usize_add(v_i_2480_, v___x_2491_);
v_i_2480_ = v___x_2492_;
v_b_2481_ = v_a_2490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2521_, lean_object* v_str_2522_, lean_object* v_as_2523_, lean_object* v_sz_2524_, lean_object* v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
size_t v_sz_boxed_2534_; size_t v_i_boxed_2535_; lean_object* v_res_2536_; 
v_sz_boxed_2534_ = lean_unbox_usize(v_sz_2524_);
lean_dec(v_sz_2524_);
v_i_boxed_2535_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_res_2536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2521_, v_str_2522_, v_as_2523_, v_sz_boxed_2534_, v_i_boxed_2535_, v_b_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_as_2523_);
lean_dec_ref(v_str_2522_);
lean_dec(v___y_2521_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_str_2545_; lean_object* v___y_2547_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_str_2545_ = l_Lean_TSyntax_getDocString(v_docstring_2537_);
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = l_Lean_Syntax_getArg(v_docstring_2537_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2563_);
lean_dec(v___x_2563_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_box(0);
v___y_2547_ = v___x_2565_;
goto v___jp_2546_;
}
else
{
lean_object* v_val_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; 
v_val_2566_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_val_2566_);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2567_ = 0;
v___x_2568_ = l_Lean_SourceInfo_getPos_x3f(v_val_2566_, v___x_2567_);
lean_dec(v_val_2566_);
v___y_2547_ = v___x_2568_;
goto v___jp_2546_;
}
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v_fst_2549_; lean_object* v___x_2550_; size_t v_sz_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
lean_inc_ref(v_str_2545_);
v___x_2548_ = l_Lean_rewriteManualLinksCore(v_str_2545_);
v_fst_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_fst_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = lean_box(0);
v_sz_2551_ = lean_array_size(v_fst_2549_);
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2547_, v_str_2545_, v_fst_2549_, v_sz_2551_, v___x_2552_, v___x_2550_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v_fst_2549_);
lean_dec_ref(v_str_2545_);
lean_dec(v___y_2547_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; 
v_unused_2561_ = lean_ctor_get(v___x_2553_, 0);
lean_dec(v_unused_2561_);
v___x_2555_ = v___x_2553_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_dec(v___x_2553_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2550_);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2550_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
else
{
return v___x_2553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v_docstring_2569_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2578_, lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_toCold_2587_; lean_object* v_currRecDepth_2588_; lean_object* v_ref_2589_; uint16_t v_optionFlags_2590_; uint8_t v_suppressElabErrors_2591_; uint8_t v_checkDeprecated_2592_; uint8_t v_isRecordingDeps_2593_; lean_object* v_ref_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_toCold_2587_ = lean_ctor_get(v___y_2584_, 0);
v_currRecDepth_2588_ = lean_ctor_get(v___y_2584_, 1);
v_ref_2589_ = lean_ctor_get(v___y_2584_, 2);
v_optionFlags_2590_ = lean_ctor_get_uint16(v___y_2584_, sizeof(void*)*3);
v_suppressElabErrors_2591_ = lean_ctor_get_uint8(v___y_2584_, sizeof(void*)*3 + 2);
v_checkDeprecated_2592_ = lean_ctor_get_uint8(v___y_2584_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2593_ = lean_ctor_get_uint8(v___y_2584_, sizeof(void*)*3 + 4);
v_ref_2594_ = l_Lean_replaceRef(v_ref_2578_, v_ref_2589_);
lean_inc(v_currRecDepth_2588_);
lean_inc_ref(v_toCold_2587_);
v___x_2595_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2595_, 0, v_toCold_2587_);
lean_ctor_set(v___x_2595_, 1, v_currRecDepth_2588_);
lean_ctor_set(v___x_2595_, 2, v_ref_2594_);
lean_ctor_set_uint16(v___x_2595_, sizeof(void*)*3, v_optionFlags_2590_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3 + 2, v_suppressElabErrors_2591_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3 + 3, v_checkDeprecated_2592_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3 + 4, v_isRecordingDeps_2593_);
v___x_2596_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___x_2595_, v___y_2585_);
lean_dec_ref_known(v___x_2595_, 3);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2597_, lean_object* v_msg_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2597_, v_msg_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v_ref_2597_);
return v_res_2606_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2609_ = l_Lean_stringToMessageData(v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_unsigned_to_nat(1u);
v___x_2626_ = l_Lean_Syntax_getArg(v_stx_2611_, v___x_2625_);
if (lean_obj_tag(v___x_2626_) == 1)
{
lean_object* v_kind_2627_; 
v_kind_2627_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_kind_2627_);
if (lean_obj_tag(v_kind_2627_) == 1)
{
lean_object* v_pre_2628_; 
v_pre_2628_ = lean_ctor_get(v_kind_2627_, 0);
lean_inc(v_pre_2628_);
if (lean_obj_tag(v_pre_2628_) == 1)
{
lean_object* v_pre_2629_; 
v_pre_2629_ = lean_ctor_get(v_pre_2628_, 0);
lean_inc(v_pre_2629_);
if (lean_obj_tag(v_pre_2629_) == 1)
{
lean_object* v_pre_2630_; 
v_pre_2630_ = lean_ctor_get(v_pre_2629_, 0);
lean_inc(v_pre_2630_);
if (lean_obj_tag(v_pre_2630_) == 1)
{
lean_object* v_pre_2631_; 
v_pre_2631_ = lean_ctor_get(v_pre_2630_, 0);
if (lean_obj_tag(v_pre_2631_) == 0)
{
lean_object* v_args_2632_; lean_object* v_str_2633_; lean_object* v_str_2634_; lean_object* v_str_2635_; lean_object* v_str_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_args_2632_ = lean_ctor_get(v___x_2626_, 2);
lean_inc_ref(v_args_2632_);
lean_dec_ref_known(v___x_2626_, 3);
v_str_2633_ = lean_ctor_get(v_kind_2627_, 1);
lean_inc_ref(v_str_2633_);
lean_dec_ref_known(v_kind_2627_, 2);
v_str_2634_ = lean_ctor_get(v_pre_2628_, 1);
lean_inc_ref(v_str_2634_);
lean_dec_ref_known(v_pre_2628_, 2);
v_str_2635_ = lean_ctor_get(v_pre_2629_, 1);
lean_inc_ref(v_str_2635_);
lean_dec_ref_known(v_pre_2629_, 2);
v_str_2636_ = lean_ctor_get(v_pre_2630_, 1);
lean_inc_ref(v_str_2636_);
lean_dec_ref_known(v_pre_2630_, 2);
v___x_2637_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2638_ = lean_string_dec_eq(v_str_2636_, v___x_2637_);
lean_dec_ref(v_str_2636_);
if (v___x_2638_ == 0)
{
lean_dec_ref(v_str_2635_);
lean_dec_ref(v_str_2634_);
lean_dec_ref(v_str_2633_);
lean_dec_ref(v_args_2632_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2639_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2640_ = lean_string_dec_eq(v_str_2635_, v___x_2639_);
lean_dec_ref(v_str_2635_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v_str_2634_);
lean_dec_ref(v_str_2633_);
lean_dec_ref(v_args_2632_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2642_ = lean_string_dec_eq(v_str_2634_, v___x_2641_);
lean_dec_ref(v_str_2634_);
if (v___x_2642_ == 0)
{
lean_dec_ref(v_str_2633_);
lean_dec_ref(v_args_2632_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2644_ = lean_string_dec_eq(v_str_2633_, v___x_2643_);
lean_dec_ref(v_str_2633_);
if (v___x_2644_ == 0)
{
lean_dec_ref(v_args_2632_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = lean_array_get_size(v_args_2632_);
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = lean_nat_dec_eq(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_dec_ref(v_args_2632_);
goto v___jp_2619_;
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_array_fget(v_args_2632_, v___x_2648_);
lean_dec_ref(v_args_2632_);
if (lean_obj_tag(v___x_2649_) == 2)
{
lean_object* v_val_2650_; lean_object* v___x_2651_; 
lean_dec(v_stx_2611_);
v_val_2650_ = lean_ctor_get(v___x_2649_, 1);
lean_inc_ref(v_val_2650_);
lean_dec_ref_known(v___x_2649_, 2);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_val_2650_);
return v___x_2651_;
}
else
{
lean_dec(v___x_2649_);
goto v___jp_2619_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2630_, 2);
lean_dec_ref_known(v_pre_2629_, 2);
lean_dec_ref_known(v_pre_2628_, 2);
lean_dec_ref_known(v_kind_2627_, 2);
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2619_;
}
}
else
{
lean_dec_ref_known(v_pre_2629_, 2);
lean_dec(v_pre_2630_);
lean_dec_ref_known(v_pre_2628_, 2);
lean_dec_ref_known(v_kind_2627_, 2);
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2619_;
}
}
else
{
lean_dec(v_pre_2629_);
lean_dec_ref_known(v_pre_2628_, 2);
lean_dec_ref_known(v_kind_2627_, 2);
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2619_;
}
}
else
{
lean_dec(v_pre_2628_);
lean_dec_ref_known(v_kind_2627_, 2);
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2619_;
}
}
else
{
lean_dec(v_kind_2627_);
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2619_;
}
}
else
{
lean_dec(v___x_2626_);
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2620_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2611_);
v___x_2621_ = l_Lean_MessageData_ofSyntax(v_stx_2611_);
v___x_2622_ = l_Lean_indentD(v___x_2621_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2620_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2611_, v___x_2623_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v_stx_2611_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2661_, lean_object* v_docComment_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v___x_2670_; 
v___x_2670_ = l_Lean_Name_isAnonymous(v_declName_2661_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___x_2736_; lean_object* v_env_2737_; lean_object* v___x_2738_; 
v___x_2671_ = 1;
v___x_2736_ = lean_st_ref_get(v___y_2668_);
v_env_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc_ref(v_env_2737_);
lean_dec(v___x_2736_);
v___x_2738_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2737_, v_declName_2661_);
lean_dec_ref(v_env_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
v___y_2673_ = v___y_2663_;
v___y_2674_ = v___y_2664_;
v___y_2675_ = v___y_2665_;
v___y_2676_ = v___y_2666_;
v___y_2677_ = v___y_2667_;
v___y_2678_ = v___y_2668_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref_known(v___x_2738_, 1);
lean_dec(v_docComment_2662_);
v___x_2739_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2740_ = l_Lean_MessageData_ofConstName(v_declName_2661_, v___x_2670_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2743_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2744_;
}
v___jp_2672_:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2662_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref_known(v___x_2679_, 1);
v___x_2680_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2662_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2727_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2727_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2727_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v_env_2686_; lean_object* v_nextMacroScope_2687_; lean_object* v_ngen_2688_; lean_object* v_auxDeclNGen_2689_; lean_object* v_traceState_2690_; lean_object* v_recordedDeps_2691_; lean_object* v_messages_2692_; lean_object* v_infoState_2693_; lean_object* v_snapshotTasks_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2725_; 
v___x_2685_ = lean_st_ref_take(v___y_2678_);
v_env_2686_ = lean_ctor_get(v___x_2685_, 0);
v_nextMacroScope_2687_ = lean_ctor_get(v___x_2685_, 1);
v_ngen_2688_ = lean_ctor_get(v___x_2685_, 2);
v_auxDeclNGen_2689_ = lean_ctor_get(v___x_2685_, 3);
v_traceState_2690_ = lean_ctor_get(v___x_2685_, 4);
v_recordedDeps_2691_ = lean_ctor_get(v___x_2685_, 6);
v_messages_2692_ = lean_ctor_get(v___x_2685_, 7);
v_infoState_2693_ = lean_ctor_get(v___x_2685_, 8);
v_snapshotTasks_2694_ = lean_ctor_get(v___x_2685_, 9);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2685_, 5);
lean_dec(v_unused_2726_);
v___x_2696_ = v___x_2685_;
v_isShared_2697_ = v_isSharedCheck_2725_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snapshotTasks_2694_);
lean_inc(v_infoState_2693_);
lean_inc(v_messages_2692_);
lean_inc(v_recordedDeps_2691_);
lean_inc(v_traceState_2690_);
lean_inc(v_auxDeclNGen_2689_);
lean_inc(v_ngen_2688_);
lean_inc(v_nextMacroScope_2687_);
lean_inc(v_env_2686_);
lean_dec(v___x_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2725_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2698_ = l_Lean_docStringExt;
v___x_2699_ = l_String_removeLeadingSpaces(v_a_2681_);
v___x_2700_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2698_, v_env_2686_, v_declName_2661_, v___x_2699_, v___x_2671_);
v___x_2701_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 5, v___x_2701_);
lean_ctor_set(v___x_2696_, 0, v___x_2700_);
v___x_2703_ = v___x_2696_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_nextMacroScope_2687_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_ngen_2688_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_auxDeclNGen_2689_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_traceState_2690_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2724_, 6, v_recordedDeps_2691_);
lean_ctor_set(v_reuseFailAlloc_2724_, 7, v_messages_2692_);
lean_ctor_set(v_reuseFailAlloc_2724_, 8, v_infoState_2693_);
lean_ctor_set(v_reuseFailAlloc_2724_, 9, v_snapshotTasks_2694_);
v___x_2703_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v_mctx_2706_; lean_object* v_zetaDeltaFVarIds_2707_; lean_object* v_postponed_2708_; lean_object* v_diag_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2722_; 
v___x_2704_ = lean_st_ref_put(v___y_2678_, v___x_2703_);
v___x_2705_ = lean_st_ref_take(v___y_2676_);
v_mctx_2706_ = lean_ctor_get(v___x_2705_, 0);
v_zetaDeltaFVarIds_2707_ = lean_ctor_get(v___x_2705_, 2);
v_postponed_2708_ = lean_ctor_get(v___x_2705_, 3);
v_diag_2709_ = lean_ctor_get(v___x_2705_, 4);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; 
v_unused_2723_ = lean_ctor_get(v___x_2705_, 1);
lean_dec(v_unused_2723_);
v___x_2711_ = v___x_2705_;
v_isShared_2712_ = v_isSharedCheck_2722_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_diag_2709_);
lean_inc(v_postponed_2708_);
lean_inc(v_zetaDeltaFVarIds_2707_);
lean_inc(v_mctx_2706_);
lean_dec(v___x_2705_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2722_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_mctx_2706_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v_zetaDeltaFVarIds_2707_);
lean_ctor_set(v_reuseFailAlloc_2721_, 3, v_postponed_2708_);
lean_ctor_set(v_reuseFailAlloc_2721_, 4, v_diag_2709_);
v___x_2716_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_st_ref_put(v___y_2676_, v___x_2716_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2713_);
v___x_2719_ = v___x_2683_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2713_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_declName_2661_);
v_a_2728_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2680_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2680_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_dec(v_docComment_2662_);
lean_dec(v_declName_2661_);
return v___x_2679_;
}
}
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v_docComment_2662_);
lean_dec(v_declName_2661_);
v___x_2745_ = lean_box(0);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2747_, lean_object* v_docComment_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2747_, v_docComment_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2757_, lean_object* v_declName_2758_, lean_object* v_binders_2759_, lean_object* v_docComment_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
if (v_isVerso_2757_ == 0)
{
lean_object* v___x_2768_; 
lean_dec(v_binders_2759_);
v___x_2768_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2758_, v_docComment_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_addVersoDocString(v_declName_2758_, v_binders_2759_, v_docComment_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
lean_dec(v_docComment_2760_);
return v___x_2769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2770_, lean_object* v_declName_2771_, lean_object* v_binders_2772_, lean_object* v_docComment_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
uint8_t v_isVerso_boxed_2781_; lean_object* v_res_2782_; 
v_isVerso_boxed_2781_ = lean_unbox(v_isVerso_2770_);
v_res_2782_ = l_Lean_addDocStringOf(v_isVerso_boxed_2781_, v_declName_2771_, v_binders_2772_, v_docComment_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2783_, lean_object* v_msgData_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2783_, v_msgData_2784_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2793_, lean_object* v_msgData_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2793_, v_msgData_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v_ref_2793_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2803_, lean_object* v_ref_2804_, lean_object* v_msg_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2804_, v_msg_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_ref_2815_, lean_object* v_msg_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2814_, v_ref_2815_, v_msg_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v_ref_2815_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2825_, lean_object* v_t_2826_){
_start:
{
if (lean_obj_tag(v_t_2826_) == 0)
{
lean_object* v_k_2827_; lean_object* v_v_2828_; lean_object* v_l_2829_; lean_object* v_r_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_3484_; 
v_k_2827_ = lean_ctor_get(v_t_2826_, 1);
v_v_2828_ = lean_ctor_get(v_t_2826_, 2);
v_l_2829_ = lean_ctor_get(v_t_2826_, 3);
v_r_2830_ = lean_ctor_get(v_t_2826_, 4);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_t_2826_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v_t_2826_, 0);
lean_dec(v_unused_3485_);
v___x_2832_ = v_t_2826_;
v_isShared_2833_ = v_isSharedCheck_3484_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_r_2830_);
lean_inc(v_l_2829_);
lean_inc(v_v_2828_);
lean_inc(v_k_2827_);
lean_dec(v_t_2826_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_3484_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
uint8_t v___x_2834_; 
v___x_2834_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2825_, v_k_2827_);
switch(v___x_2834_)
{
case 0:
{
lean_object* v_impl_2835_; lean_object* v___x_2836_; 
v_impl_2835_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2825_, v_l_2829_);
v___x_2836_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2835_) == 0)
{
if (lean_obj_tag(v_r_2830_) == 0)
{
lean_object* v_size_2837_; lean_object* v_size_2838_; lean_object* v_k_2839_; lean_object* v_v_2840_; lean_object* v_l_2841_; lean_object* v_r_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_size_2837_ = lean_ctor_get(v_impl_2835_, 0);
v_size_2838_ = lean_ctor_get(v_r_2830_, 0);
v_k_2839_ = lean_ctor_get(v_r_2830_, 1);
v_v_2840_ = lean_ctor_get(v_r_2830_, 2);
v_l_2841_ = lean_ctor_get(v_r_2830_, 3);
lean_inc(v_l_2841_);
v_r_2842_ = lean_ctor_get(v_r_2830_, 4);
v___x_2843_ = lean_unsigned_to_nat(3u);
v___x_2844_ = lean_nat_mul(v___x_2843_, v_size_2837_);
v___x_2845_ = lean_nat_dec_lt(v___x_2844_, v_size_2838_);
lean_dec(v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
lean_dec(v_l_2841_);
v___x_2846_ = lean_nat_add(v___x_2836_, v_size_2837_);
v___x_2847_ = lean_nat_add(v___x_2846_, v_size_2838_);
lean_dec(v___x_2846_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 3, v_impl_2835_);
lean_ctor_set(v___x_2832_, 0, v___x_2847_);
v___x_2849_ = v___x_2832_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_impl_2835_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_r_2830_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2914_; 
lean_inc(v_r_2842_);
lean_inc(v_v_2840_);
lean_inc(v_k_2839_);
lean_inc(v_size_2838_);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; lean_object* v_unused_2919_; 
v_unused_2915_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_r_2830_, 2);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_r_2830_, 1);
lean_dec(v_unused_2918_);
v_unused_2919_ = lean_ctor_get(v_r_2830_, 0);
lean_dec(v_unused_2919_);
v___x_2852_ = v_r_2830_;
v_isShared_2853_ = v_isSharedCheck_2914_;
goto v_resetjp_2851_;
}
else
{
lean_dec(v_r_2830_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2914_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_size_2854_; lean_object* v_k_2855_; lean_object* v_v_2856_; lean_object* v_l_2857_; lean_object* v_r_2858_; lean_object* v_size_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_size_2854_ = lean_ctor_get(v_l_2841_, 0);
v_k_2855_ = lean_ctor_get(v_l_2841_, 1);
v_v_2856_ = lean_ctor_get(v_l_2841_, 2);
v_l_2857_ = lean_ctor_get(v_l_2841_, 3);
v_r_2858_ = lean_ctor_get(v_l_2841_, 4);
v_size_2859_ = lean_ctor_get(v_r_2842_, 0);
v___x_2860_ = lean_unsigned_to_nat(2u);
v___x_2861_ = lean_nat_mul(v___x_2860_, v_size_2859_);
v___x_2862_ = lean_nat_dec_lt(v_size_2854_, v___x_2861_);
lean_dec(v___x_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2890_; 
lean_inc(v_r_2858_);
lean_inc(v_l_2857_);
lean_inc(v_v_2856_);
lean_inc(v_k_2855_);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_l_2841_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; lean_object* v_unused_2892_; lean_object* v_unused_2893_; lean_object* v_unused_2894_; lean_object* v_unused_2895_; 
v_unused_2891_ = lean_ctor_get(v_l_2841_, 4);
lean_dec(v_unused_2891_);
v_unused_2892_ = lean_ctor_get(v_l_2841_, 3);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_l_2841_, 2);
lean_dec(v_unused_2893_);
v_unused_2894_ = lean_ctor_get(v_l_2841_, 1);
lean_dec(v_unused_2894_);
v_unused_2895_ = lean_ctor_get(v_l_2841_, 0);
lean_dec(v_unused_2895_);
v___x_2864_ = v_l_2841_;
v_isShared_2865_ = v_isSharedCheck_2890_;
goto v_resetjp_2863_;
}
else
{
lean_dec(v_l_2841_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2890_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2880_; 
v___x_2866_ = lean_nat_add(v___x_2836_, v_size_2837_);
v___x_2867_ = lean_nat_add(v___x_2866_, v_size_2838_);
lean_dec(v_size_2838_);
if (lean_obj_tag(v_l_2857_) == 0)
{
lean_object* v_size_2888_; 
v_size_2888_ = lean_ctor_get(v_l_2857_, 0);
lean_inc(v_size_2888_);
v___y_2880_ = v_size_2888_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_unsigned_to_nat(0u);
v___y_2880_ = v___x_2889_;
goto v___jp_2879_;
}
v___jp_2868_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_nat_add(v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec(v___y_2870_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 4, v_r_2842_);
lean_ctor_set(v___x_2864_, 3, v_r_2858_);
lean_ctor_set(v___x_2864_, 2, v_v_2840_);
lean_ctor_set(v___x_2864_, 1, v_k_2839_);
lean_ctor_set(v___x_2864_, 0, v___x_2872_);
v___x_2874_ = v___x_2864_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_k_2839_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v_v_2840_);
lean_ctor_set(v_reuseFailAlloc_2878_, 3, v_r_2858_);
lean_ctor_set(v_reuseFailAlloc_2878_, 4, v_r_2842_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 4, v___x_2874_);
lean_ctor_set(v___x_2852_, 3, v___y_2869_);
lean_ctor_set(v___x_2852_, 2, v_v_2856_);
lean_ctor_set(v___x_2852_, 1, v_k_2855_);
lean_ctor_set(v___x_2852_, 0, v___x_2867_);
v___x_2876_ = v___x_2852_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2855_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2856_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v___y_2869_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_nat_add(v___x_2866_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec(v___x_2866_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_l_2857_);
lean_ctor_set(v___x_2832_, 3, v_impl_2835_);
lean_ctor_set(v___x_2832_, 0, v___x_2881_);
v___x_2883_ = v___x_2832_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_impl_2835_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_l_2857_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_nat_add(v___x_2836_, v_size_2859_);
if (lean_obj_tag(v_r_2858_) == 0)
{
lean_object* v_size_2885_; 
v_size_2885_ = lean_ctor_get(v_r_2858_, 0);
lean_inc(v_size_2885_);
v___y_2869_ = v___x_2883_;
v___y_2870_ = v___x_2884_;
v___y_2871_ = v_size_2885_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2886_; 
v___x_2886_ = lean_unsigned_to_nat(0u);
v___y_2869_ = v___x_2883_;
v___y_2870_ = v___x_2884_;
v___y_2871_ = v___x_2886_;
goto v___jp_2868_;
}
}
}
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
lean_del_object(v___x_2832_);
v___x_2896_ = lean_nat_add(v___x_2836_, v_size_2837_);
v___x_2897_ = lean_nat_add(v___x_2896_, v_size_2838_);
lean_dec(v_size_2838_);
v___x_2898_ = lean_nat_add(v___x_2896_, v_size_2854_);
lean_dec(v___x_2896_);
lean_inc_ref(v_impl_2835_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 4, v_l_2841_);
lean_ctor_set(v___x_2852_, 3, v_impl_2835_);
lean_ctor_set(v___x_2852_, 2, v_v_2828_);
lean_ctor_set(v___x_2852_, 1, v_k_2827_);
lean_ctor_set(v___x_2852_, 0, v___x_2898_);
v___x_2900_ = v___x_2852_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_impl_2835_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_l_2841_);
v___x_2900_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_isSharedCheck_2907_ = !lean_is_exclusive(v_impl_2835_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; lean_object* v_unused_2909_; lean_object* v_unused_2910_; lean_object* v_unused_2911_; lean_object* v_unused_2912_; 
v_unused_2908_ = lean_ctor_get(v_impl_2835_, 4);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_impl_2835_, 3);
lean_dec(v_unused_2909_);
v_unused_2910_ = lean_ctor_get(v_impl_2835_, 2);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_impl_2835_, 1);
lean_dec(v_unused_2911_);
v_unused_2912_ = lean_ctor_get(v_impl_2835_, 0);
lean_dec(v_unused_2912_);
v___x_2902_ = v_impl_2835_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_dec(v_impl_2835_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 4, v_r_2842_);
lean_ctor_set(v___x_2902_, 3, v___x_2900_);
lean_ctor_set(v___x_2902_, 2, v_v_2840_);
lean_ctor_set(v___x_2902_, 1, v_k_2839_);
lean_ctor_set(v___x_2902_, 0, v___x_2897_);
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_k_2839_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_v_2840_);
lean_ctor_set(v_reuseFailAlloc_2906_, 3, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2906_, 4, v_r_2842_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v_size_2920_ = lean_ctor_get(v_impl_2835_, 0);
v___x_2921_ = lean_nat_add(v___x_2836_, v_size_2920_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 3, v_impl_2835_);
lean_ctor_set(v___x_2832_, 0, v___x_2921_);
v___x_2923_ = v___x_2832_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2924_, 3, v_impl_2835_);
lean_ctor_set(v_reuseFailAlloc_2924_, 4, v_r_2830_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
else
{
if (lean_obj_tag(v_r_2830_) == 0)
{
lean_object* v_l_2925_; 
v_l_2925_ = lean_ctor_get(v_r_2830_, 3);
lean_inc(v_l_2925_);
if (lean_obj_tag(v_l_2925_) == 0)
{
lean_object* v_r_2926_; 
v_r_2926_ = lean_ctor_get(v_r_2830_, 4);
lean_inc(v_r_2926_);
if (lean_obj_tag(v_r_2926_) == 0)
{
lean_object* v_size_2927_; lean_object* v_k_2928_; lean_object* v_v_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2942_; 
v_size_2927_ = lean_ctor_get(v_r_2830_, 0);
v_k_2928_ = lean_ctor_get(v_r_2830_, 1);
v_v_2929_ = lean_ctor_get(v_r_2830_, 2);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_2942_ == 0)
{
lean_object* v_unused_2943_; lean_object* v_unused_2944_; 
v_unused_2943_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_2944_);
v___x_2931_ = v_r_2830_;
v_isShared_2932_ = v_isSharedCheck_2942_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_v_2929_);
lean_inc(v_k_2928_);
lean_inc(v_size_2927_);
lean_dec(v_r_2830_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2942_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v_size_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v_size_2933_ = lean_ctor_get(v_l_2925_, 0);
v___x_2934_ = lean_nat_add(v___x_2836_, v_size_2927_);
lean_dec(v_size_2927_);
v___x_2935_ = lean_nat_add(v___x_2836_, v_size_2933_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 4, v_l_2925_);
lean_ctor_set(v___x_2931_, 3, v_impl_2835_);
lean_ctor_set(v___x_2931_, 2, v_v_2828_);
lean_ctor_set(v___x_2931_, 1, v_k_2827_);
lean_ctor_set(v___x_2931_, 0, v___x_2935_);
v___x_2937_ = v___x_2931_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2941_, 3, v_impl_2835_);
lean_ctor_set(v_reuseFailAlloc_2941_, 4, v_l_2925_);
v___x_2937_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2939_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_r_2926_);
lean_ctor_set(v___x_2832_, 3, v___x_2937_);
lean_ctor_set(v___x_2832_, 2, v_v_2929_);
lean_ctor_set(v___x_2832_, 1, v_k_2928_);
lean_ctor_set(v___x_2832_, 0, v___x_2934_);
v___x_2939_ = v___x_2832_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v___x_2937_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_r_2926_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_k_2945_; lean_object* v_v_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2969_; 
v_k_2945_ = lean_ctor_get(v_r_2830_, 1);
v_v_2946_ = lean_ctor_get(v_r_2830_, 2);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; lean_object* v_unused_2971_; lean_object* v_unused_2972_; 
v_unused_2970_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_2970_);
v_unused_2971_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_2971_);
v_unused_2972_ = lean_ctor_get(v_r_2830_, 0);
lean_dec(v_unused_2972_);
v___x_2948_ = v_r_2830_;
v_isShared_2949_ = v_isSharedCheck_2969_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_v_2946_);
lean_inc(v_k_2945_);
lean_dec(v_r_2830_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2969_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_k_2950_; lean_object* v_v_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2965_; 
v_k_2950_ = lean_ctor_get(v_l_2925_, 1);
v_v_2951_ = lean_ctor_get(v_l_2925_, 2);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_l_2925_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; lean_object* v_unused_2968_; 
v_unused_2966_ = lean_ctor_get(v_l_2925_, 4);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_l_2925_, 3);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_l_2925_, 0);
lean_dec(v_unused_2968_);
v___x_2953_ = v_l_2925_;
v_isShared_2954_ = v_isSharedCheck_2965_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_v_2951_);
lean_inc(v_k_2950_);
lean_dec(v_l_2925_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2965_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2955_ = lean_unsigned_to_nat(3u);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 4, v_r_2926_);
lean_ctor_set(v___x_2953_, 3, v_r_2926_);
lean_ctor_set(v___x_2953_, 2, v_v_2828_);
lean_ctor_set(v___x_2953_, 1, v_k_2827_);
lean_ctor_set(v___x_2953_, 0, v___x_2836_);
v___x_2957_ = v___x_2953_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_r_2926_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_r_2926_);
v___x_2957_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2959_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 3, v_r_2926_);
lean_ctor_set(v___x_2948_, 0, v___x_2836_);
v___x_2959_ = v___x_2948_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_k_2945_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_v_2946_);
lean_ctor_set(v_reuseFailAlloc_2963_, 3, v_r_2926_);
lean_ctor_set(v_reuseFailAlloc_2963_, 4, v_r_2926_);
v___x_2959_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v___x_2959_);
lean_ctor_set(v___x_2832_, 3, v___x_2957_);
lean_ctor_set(v___x_2832_, 2, v_v_2951_);
lean_ctor_set(v___x_2832_, 1, v_k_2950_);
lean_ctor_set(v___x_2832_, 0, v___x_2955_);
v___x_2961_ = v___x_2832_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_k_2950_);
lean_ctor_set(v_reuseFailAlloc_2962_, 2, v_v_2951_);
lean_ctor_set(v_reuseFailAlloc_2962_, 3, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2962_, 4, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2973_; 
v_r_2973_ = lean_ctor_get(v_r_2830_, 4);
lean_inc(v_r_2973_);
if (lean_obj_tag(v_r_2973_) == 0)
{
lean_object* v_k_2974_; lean_object* v_v_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2986_; 
v_k_2974_ = lean_ctor_get(v_r_2830_, 1);
v_v_2975_ = lean_ctor_get(v_r_2830_, 2);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; lean_object* v_unused_2988_; lean_object* v_unused_2989_; 
v_unused_2987_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_2987_);
v_unused_2988_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_r_2830_, 0);
lean_dec(v_unused_2989_);
v___x_2977_ = v_r_2830_;
v_isShared_2978_ = v_isSharedCheck_2986_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_v_2975_);
lean_inc(v_k_2974_);
lean_dec(v_r_2830_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2986_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2979_ = lean_unsigned_to_nat(3u);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 4, v_l_2925_);
lean_ctor_set(v___x_2977_, 2, v_v_2828_);
lean_ctor_set(v___x_2977_, 1, v_k_2827_);
lean_ctor_set(v___x_2977_, 0, v___x_2836_);
v___x_2981_ = v___x_2977_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_l_2925_);
v___x_2981_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_r_2973_);
lean_ctor_set(v___x_2832_, 3, v___x_2981_);
lean_ctor_set(v___x_2832_, 2, v_v_2975_);
lean_ctor_set(v___x_2832_, 1, v_k_2974_);
lean_ctor_set(v___x_2832_, 0, v___x_2979_);
v___x_2983_ = v___x_2832_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_k_2974_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_v_2975_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_r_2973_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_size_2990_; lean_object* v_k_2991_; lean_object* v_v_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3003_; 
v_size_2990_ = lean_ctor_get(v_r_2830_, 0);
v_k_2991_ = lean_ctor_get(v_r_2830_, 1);
v_v_2992_ = lean_ctor_get(v_r_2830_, 2);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_3003_ == 0)
{
lean_object* v_unused_3004_; lean_object* v_unused_3005_; 
v_unused_3004_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_3005_);
v___x_2994_ = v_r_2830_;
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_v_2992_);
lean_inc(v_k_2991_);
lean_inc(v_size_2990_);
lean_dec(v_r_2830_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 3, v_r_2973_);
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_size_2990_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_k_2991_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v_v_2992_);
lean_ctor_set(v_reuseFailAlloc_3002_, 3, v_r_2973_);
lean_ctor_set(v_reuseFailAlloc_3002_, 4, v_r_2973_);
v___x_2997_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = lean_unsigned_to_nat(2u);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v___x_2997_);
lean_ctor_set(v___x_2832_, 3, v_r_2973_);
lean_ctor_set(v___x_2832_, 0, v___x_2998_);
v___x_3000_ = v___x_2832_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3001_, 3, v_r_2973_);
lean_ctor_set(v_reuseFailAlloc_3001_, 4, v___x_2997_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
else
{
lean_object* v___x_3007_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 3, v_r_2830_);
lean_ctor_set(v___x_2832_, 0, v___x_2836_);
v___x_3007_ = v___x_2832_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_r_2830_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v_r_2830_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2832_);
lean_dec(v_v_2828_);
lean_dec(v_k_2827_);
if (lean_obj_tag(v_l_2829_) == 0)
{
if (lean_obj_tag(v_r_2830_) == 0)
{
lean_object* v_size_3009_; lean_object* v_k_3010_; lean_object* v_v_3011_; lean_object* v_l_3012_; lean_object* v_r_3013_; lean_object* v_size_3014_; lean_object* v_k_3015_; lean_object* v_v_3016_; lean_object* v_l_3017_; lean_object* v_r_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_size_3009_ = lean_ctor_get(v_l_2829_, 0);
v_k_3010_ = lean_ctor_get(v_l_2829_, 1);
v_v_3011_ = lean_ctor_get(v_l_2829_, 2);
v_l_3012_ = lean_ctor_get(v_l_2829_, 3);
v_r_3013_ = lean_ctor_get(v_l_2829_, 4);
lean_inc(v_r_3013_);
v_size_3014_ = lean_ctor_get(v_r_2830_, 0);
v_k_3015_ = lean_ctor_get(v_r_2830_, 1);
v_v_3016_ = lean_ctor_get(v_r_2830_, 2);
v_l_3017_ = lean_ctor_get(v_r_2830_, 3);
lean_inc(v_l_3017_);
v_r_3018_ = lean_ctor_get(v_r_2830_, 4);
v___x_3019_ = lean_unsigned_to_nat(1u);
v___x_3020_ = lean_nat_dec_lt(v_size_3009_, v_size_3014_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3156_; 
lean_inc(v_l_3012_);
lean_inc(v_v_3011_);
lean_inc(v_k_3010_);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; lean_object* v_unused_3161_; 
v_unused_3157_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_l_2829_, 2);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_l_2829_, 1);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3161_);
v___x_3022_ = v_l_2829_;
v_isShared_3023_ = v_isSharedCheck_3156_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v_l_2829_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3156_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v_tree_3025_; 
v___x_3024_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3010_, v_v_3011_, v_l_3012_, v_r_3013_);
v_tree_3025_ = lean_ctor_get(v___x_3024_, 2);
if (lean_obj_tag(v_tree_3025_) == 0)
{
lean_object* v_k_3026_; lean_object* v_v_3027_; lean_object* v_size_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
lean_inc_ref(v_tree_3025_);
v_k_3026_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_k_3026_);
v_v_3027_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_v_3027_);
lean_dec_ref(v___x_3024_);
v_size_3028_ = lean_ctor_get(v_tree_3025_, 0);
v___x_3029_ = lean_unsigned_to_nat(3u);
v___x_3030_ = lean_nat_mul(v___x_3029_, v_size_3028_);
v___x_3031_ = lean_nat_dec_lt(v___x_3030_, v_size_3014_);
lean_dec(v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_dec(v_l_3017_);
v___x_3032_ = lean_nat_add(v___x_3019_, v_size_3028_);
v___x_3033_ = lean_nat_add(v___x_3032_, v_size_3014_);
lean_dec(v___x_3032_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v_r_2830_);
lean_ctor_set(v___x_3022_, 3, v_tree_3025_);
lean_ctor_set(v___x_3022_, 2, v_v_3027_);
lean_ctor_set(v___x_3022_, 1, v_k_3026_);
lean_ctor_set(v___x_3022_, 0, v___x_3033_);
v___x_3035_ = v___x_3022_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_3026_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_3027_);
lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_tree_3025_);
lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_r_2830_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
else
{
lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3091_; 
lean_inc(v_r_3018_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
lean_inc(v_size_3014_);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; lean_object* v_unused_3093_; lean_object* v_unused_3094_; lean_object* v_unused_3095_; lean_object* v_unused_3096_; 
v_unused_3092_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_r_2830_, 2);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_r_2830_, 1);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_r_2830_, 0);
lean_dec(v_unused_3096_);
v___x_3038_ = v_r_2830_;
v_isShared_3039_ = v_isSharedCheck_3091_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v_r_2830_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3091_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_size_3040_; lean_object* v_k_3041_; lean_object* v_v_3042_; lean_object* v_l_3043_; lean_object* v_r_3044_; lean_object* v_size_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v_size_3040_ = lean_ctor_get(v_l_3017_, 0);
v_k_3041_ = lean_ctor_get(v_l_3017_, 1);
v_v_3042_ = lean_ctor_get(v_l_3017_, 2);
v_l_3043_ = lean_ctor_get(v_l_3017_, 3);
v_r_3044_ = lean_ctor_get(v_l_3017_, 4);
v_size_3045_ = lean_ctor_get(v_r_3018_, 0);
v___x_3046_ = lean_unsigned_to_nat(2u);
v___x_3047_ = lean_nat_mul(v___x_3046_, v_size_3045_);
v___x_3048_ = lean_nat_dec_lt(v_size_3040_, v___x_3047_);
lean_dec(v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3076_; 
lean_inc(v_r_3044_);
lean_inc(v_l_3043_);
lean_inc(v_v_3042_);
lean_inc(v_k_3041_);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_l_3017_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; lean_object* v_unused_3078_; lean_object* v_unused_3079_; lean_object* v_unused_3080_; lean_object* v_unused_3081_; 
v_unused_3077_ = lean_ctor_get(v_l_3017_, 4);
lean_dec(v_unused_3077_);
v_unused_3078_ = lean_ctor_get(v_l_3017_, 3);
lean_dec(v_unused_3078_);
v_unused_3079_ = lean_ctor_get(v_l_3017_, 2);
lean_dec(v_unused_3079_);
v_unused_3080_ = lean_ctor_get(v_l_3017_, 1);
lean_dec(v_unused_3080_);
v_unused_3081_ = lean_ctor_get(v_l_3017_, 0);
lean_dec(v_unused_3081_);
v___x_3050_ = v_l_3017_;
v_isShared_3051_ = v_isSharedCheck_3076_;
goto v_resetjp_3049_;
}
else
{
lean_dec(v_l_3017_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3076_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3066_; 
v___x_3052_ = lean_nat_add(v___x_3019_, v_size_3028_);
v___x_3053_ = lean_nat_add(v___x_3052_, v_size_3014_);
lean_dec(v_size_3014_);
if (lean_obj_tag(v_l_3043_) == 0)
{
lean_object* v_size_3074_; 
v_size_3074_ = lean_ctor_get(v_l_3043_, 0);
lean_inc(v_size_3074_);
v___y_3066_ = v_size_3074_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v___y_3066_ = v___x_3075_;
goto v___jp_3065_;
}
v___jp_3054_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_nat_add(v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec(v___y_3056_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 4, v_r_3018_);
lean_ctor_set(v___x_3050_, 3, v_r_3044_);
lean_ctor_set(v___x_3050_, 2, v_v_3016_);
lean_ctor_set(v___x_3050_, 1, v_k_3015_);
lean_ctor_set(v___x_3050_, 0, v___x_3058_);
v___x_3060_ = v___x_3050_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_r_3044_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_r_3018_);
v___x_3060_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3062_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 4, v___x_3060_);
lean_ctor_set(v___x_3038_, 3, v___y_3055_);
lean_ctor_set(v___x_3038_, 2, v_v_3042_);
lean_ctor_set(v___x_3038_, 1, v_k_3041_);
lean_ctor_set(v___x_3038_, 0, v___x_3053_);
v___x_3062_ = v___x_3038_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_k_3041_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_v_3042_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v___y_3055_);
lean_ctor_set(v_reuseFailAlloc_3063_, 4, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
v___jp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3067_ = lean_nat_add(v___x_3052_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec(v___x_3052_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v_l_3043_);
lean_ctor_set(v___x_3022_, 3, v_tree_3025_);
lean_ctor_set(v___x_3022_, 2, v_v_3027_);
lean_ctor_set(v___x_3022_, 1, v_k_3026_);
lean_ctor_set(v___x_3022_, 0, v___x_3067_);
v___x_3069_ = v___x_3022_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_k_3026_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_v_3027_);
lean_ctor_set(v_reuseFailAlloc_3073_, 3, v_tree_3025_);
lean_ctor_set(v_reuseFailAlloc_3073_, 4, v_l_3043_);
v___x_3069_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_nat_add(v___x_3019_, v_size_3045_);
if (lean_obj_tag(v_r_3044_) == 0)
{
lean_object* v_size_3071_; 
v_size_3071_ = lean_ctor_get(v_r_3044_, 0);
lean_inc(v_size_3071_);
v___y_3055_ = v___x_3069_;
v___y_3056_ = v___x_3070_;
v___y_3057_ = v_size_3071_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_unsigned_to_nat(0u);
v___y_3055_ = v___x_3069_;
v___y_3056_ = v___x_3070_;
v___y_3057_ = v___x_3072_;
goto v___jp_3054_;
}
}
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3082_ = lean_nat_add(v___x_3019_, v_size_3028_);
v___x_3083_ = lean_nat_add(v___x_3082_, v_size_3014_);
lean_dec(v_size_3014_);
v___x_3084_ = lean_nat_add(v___x_3082_, v_size_3040_);
lean_dec(v___x_3082_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 4, v_l_3017_);
lean_ctor_set(v___x_3038_, 3, v_tree_3025_);
lean_ctor_set(v___x_3038_, 2, v_v_3027_);
lean_ctor_set(v___x_3038_, 1, v_k_3026_);
lean_ctor_set(v___x_3038_, 0, v___x_3084_);
v___x_3086_ = v___x_3038_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_k_3026_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v_v_3027_);
lean_ctor_set(v_reuseFailAlloc_3090_, 3, v_tree_3025_);
lean_ctor_set(v_reuseFailAlloc_3090_, 4, v_l_3017_);
v___x_3086_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v_r_3018_);
lean_ctor_set(v___x_3022_, 3, v___x_3086_);
lean_ctor_set(v___x_3022_, 2, v_v_3016_);
lean_ctor_set(v___x_3022_, 1, v_k_3015_);
lean_ctor_set(v___x_3022_, 0, v___x_3083_);
v___x_3088_ = v___x_3022_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_r_3018_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
else
{
lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3150_; 
lean_inc(v_r_3018_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
lean_inc(v_size_3014_);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; 
v_unused_3151_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_r_2830_, 2);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_r_2830_, 1);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_r_2830_, 0);
lean_dec(v_unused_3155_);
v___x_3098_ = v_r_2830_;
v_isShared_3099_ = v_isSharedCheck_3150_;
goto v_resetjp_3097_;
}
else
{
lean_dec(v_r_2830_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3150_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
if (lean_obj_tag(v_l_3017_) == 0)
{
if (lean_obj_tag(v_r_3018_) == 0)
{
lean_object* v_k_3100_; lean_object* v_v_3101_; lean_object* v_size_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_inc(v_tree_3025_);
v_k_3100_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_k_3100_);
v_v_3101_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_v_3101_);
lean_dec_ref(v___x_3024_);
v_size_3102_ = lean_ctor_get(v_l_3017_, 0);
v___x_3103_ = lean_nat_add(v___x_3019_, v_size_3014_);
lean_dec(v_size_3014_);
v___x_3104_ = lean_nat_add(v___x_3019_, v_size_3102_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 4, v_l_3017_);
lean_ctor_set(v___x_3098_, 3, v_tree_3025_);
lean_ctor_set(v___x_3098_, 2, v_v_3101_);
lean_ctor_set(v___x_3098_, 1, v_k_3100_);
lean_ctor_set(v___x_3098_, 0, v___x_3104_);
v___x_3106_ = v___x_3098_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_k_3100_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_v_3101_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_tree_3025_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_l_3017_);
v___x_3106_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3108_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v_r_3018_);
lean_ctor_set(v___x_3022_, 3, v___x_3106_);
lean_ctor_set(v___x_3022_, 2, v_v_3016_);
lean_ctor_set(v___x_3022_, 1, v_k_3015_);
lean_ctor_set(v___x_3022_, 0, v___x_3103_);
v___x_3108_ = v___x_3022_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_r_3018_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v_k_3111_; lean_object* v_v_3112_; lean_object* v_k_3113_; lean_object* v_v_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_size_3014_);
v_k_3111_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_k_3111_);
v_v_3112_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_v_3112_);
lean_dec_ref(v___x_3024_);
v_k_3113_ = lean_ctor_get(v_l_3017_, 1);
v_v_3114_ = lean_ctor_get(v_l_3017_, 2);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_l_3017_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; 
v_unused_3129_ = lean_ctor_get(v_l_3017_, 4);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_l_3017_, 3);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_l_3017_, 0);
lean_dec(v_unused_3131_);
v___x_3116_ = v_l_3017_;
v_isShared_3117_ = v_isSharedCheck_3128_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_v_3114_);
lean_inc(v_k_3113_);
lean_dec(v_l_3017_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3128_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_unsigned_to_nat(3u);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 4, v_r_3018_);
lean_ctor_set(v___x_3116_, 3, v_r_3018_);
lean_ctor_set(v___x_3116_, 2, v_v_3112_);
lean_ctor_set(v___x_3116_, 1, v_k_3111_);
lean_ctor_set(v___x_3116_, 0, v___x_3019_);
v___x_3120_ = v___x_3116_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_k_3111_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_v_3112_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v_r_3018_);
v___x_3120_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3122_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 3, v_r_3018_);
lean_ctor_set(v___x_3098_, 0, v___x_3019_);
v___x_3122_ = v___x_3098_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3126_, 4, v_r_3018_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v___x_3122_);
lean_ctor_set(v___x_3022_, 3, v___x_3120_);
lean_ctor_set(v___x_3022_, 2, v_v_3114_);
lean_ctor_set(v___x_3022_, 1, v_k_3113_);
lean_ctor_set(v___x_3022_, 0, v___x_3118_);
v___x_3124_ = v___x_3022_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_k_3113_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_v_3114_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3018_) == 0)
{
lean_object* v_k_3132_; lean_object* v_v_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec(v_size_3014_);
v_k_3132_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_k_3132_);
v_v_3133_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_v_3133_);
lean_dec_ref(v___x_3024_);
v___x_3134_ = lean_unsigned_to_nat(3u);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 4, v_l_3017_);
lean_ctor_set(v___x_3098_, 2, v_v_3133_);
lean_ctor_set(v___x_3098_, 1, v_k_3132_);
lean_ctor_set(v___x_3098_, 0, v___x_3019_);
v___x_3136_ = v___x_3098_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_k_3132_);
lean_ctor_set(v_reuseFailAlloc_3140_, 2, v_v_3133_);
lean_ctor_set(v_reuseFailAlloc_3140_, 3, v_l_3017_);
lean_ctor_set(v_reuseFailAlloc_3140_, 4, v_l_3017_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v_r_3018_);
lean_ctor_set(v___x_3022_, 3, v___x_3136_);
lean_ctor_set(v___x_3022_, 2, v_v_3016_);
lean_ctor_set(v___x_3022_, 1, v_k_3015_);
lean_ctor_set(v___x_3022_, 0, v___x_3134_);
v___x_3138_ = v___x_3022_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_r_3018_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_object* v_k_3141_; lean_object* v_v_3142_; lean_object* v___x_3144_; 
v_k_3141_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_k_3141_);
v_v_3142_ = lean_ctor_get(v___x_3024_, 1);
lean_inc(v_v_3142_);
lean_dec_ref(v___x_3024_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 3, v_r_3018_);
v___x_3144_ = v___x_3098_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_size_3014_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_r_3018_);
v___x_3144_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_unsigned_to_nat(2u);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 4, v___x_3144_);
lean_ctor_set(v___x_3022_, 3, v_r_3018_);
lean_ctor_set(v___x_3022_, 2, v_v_3142_);
lean_ctor_set(v___x_3022_, 1, v_k_3141_);
lean_ctor_set(v___x_3022_, 0, v___x_3145_);
v___x_3147_ = v___x_3022_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_k_3141_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_v_3142_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_r_3018_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v___x_3144_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
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
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3314_; 
lean_inc(v_r_3018_);
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_r_2830_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; lean_object* v_unused_3316_; lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; 
v_unused_3315_ = lean_ctor_get(v_r_2830_, 4);
lean_dec(v_unused_3315_);
v_unused_3316_ = lean_ctor_get(v_r_2830_, 3);
lean_dec(v_unused_3316_);
v_unused_3317_ = lean_ctor_get(v_r_2830_, 2);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_r_2830_, 1);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_r_2830_, 0);
lean_dec(v_unused_3319_);
v___x_3163_ = v_r_2830_;
v_isShared_3164_ = v_isSharedCheck_3314_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v_r_2830_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3314_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v_tree_3166_; 
v___x_3165_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3015_, v_v_3016_, v_l_3017_, v_r_3018_);
v_tree_3166_ = lean_ctor_get(v___x_3165_, 2);
lean_inc(v_tree_3166_);
if (lean_obj_tag(v_tree_3166_) == 0)
{
lean_object* v_k_3167_; lean_object* v_v_3168_; lean_object* v_size_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_k_3167_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_k_3167_);
v_v_3168_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_v_3168_);
lean_dec_ref(v___x_3165_);
v_size_3169_ = lean_ctor_get(v_tree_3166_, 0);
v___x_3170_ = lean_unsigned_to_nat(3u);
v___x_3171_ = lean_nat_mul(v___x_3170_, v_size_3169_);
v___x_3172_ = lean_nat_dec_lt(v___x_3171_, v_size_3009_);
lean_dec(v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
lean_dec(v_r_3013_);
v___x_3173_ = lean_nat_add(v___x_3019_, v_size_3009_);
v___x_3174_ = lean_nat_add(v___x_3173_, v_size_3169_);
lean_dec(v___x_3173_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_tree_3166_);
lean_ctor_set(v___x_3163_, 3, v_l_2829_);
lean_ctor_set(v___x_3163_, 2, v_v_3168_);
lean_ctor_set(v___x_3163_, 1, v_k_3167_);
lean_ctor_set(v___x_3163_, 0, v___x_3174_);
v___x_3176_ = v___x_3163_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_l_2829_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_tree_3166_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
else
{
lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3243_; 
lean_inc(v_l_3012_);
lean_inc(v_v_3011_);
lean_inc(v_k_3010_);
lean_inc(v_size_3009_);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; lean_object* v_unused_3245_; lean_object* v_unused_3246_; lean_object* v_unused_3247_; lean_object* v_unused_3248_; 
v_unused_3244_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3244_);
v_unused_3245_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_l_2829_, 2);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_l_2829_, 1);
lean_dec(v_unused_3247_);
v_unused_3248_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3248_);
v___x_3179_ = v_l_2829_;
v_isShared_3180_ = v_isSharedCheck_3243_;
goto v_resetjp_3178_;
}
else
{
lean_dec(v_l_2829_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3243_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_size_3181_; lean_object* v_size_3182_; lean_object* v_k_3183_; lean_object* v_v_3184_; lean_object* v_l_3185_; lean_object* v_r_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_size_3181_ = lean_ctor_get(v_l_3012_, 0);
v_size_3182_ = lean_ctor_get(v_r_3013_, 0);
v_k_3183_ = lean_ctor_get(v_r_3013_, 1);
v_v_3184_ = lean_ctor_get(v_r_3013_, 2);
v_l_3185_ = lean_ctor_get(v_r_3013_, 3);
v_r_3186_ = lean_ctor_get(v_r_3013_, 4);
v___x_3187_ = lean_unsigned_to_nat(2u);
v___x_3188_ = lean_nat_mul(v___x_3187_, v_size_3181_);
v___x_3189_ = lean_nat_dec_lt(v_size_3182_, v___x_3188_);
lean_dec(v___x_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3227_; 
lean_inc(v_r_3186_);
lean_inc(v_l_3185_);
lean_inc(v_v_3184_);
lean_inc(v_k_3183_);
lean_del_object(v___x_3179_);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_r_3013_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; lean_object* v_unused_3229_; lean_object* v_unused_3230_; lean_object* v_unused_3231_; lean_object* v_unused_3232_; 
v_unused_3228_ = lean_ctor_get(v_r_3013_, 4);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_r_3013_, 3);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v_r_3013_, 2);
lean_dec(v_unused_3230_);
v_unused_3231_ = lean_ctor_get(v_r_3013_, 1);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v_r_3013_, 0);
lean_dec(v_unused_3232_);
v___x_3191_ = v_r_3013_;
v_isShared_3192_ = v_isSharedCheck_3227_;
goto v_resetjp_3190_;
}
else
{
lean_dec(v_r_3013_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3227_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___x_3215_; lean_object* v___y_3217_; 
v___x_3193_ = lean_nat_add(v___x_3019_, v_size_3009_);
lean_dec(v_size_3009_);
v___x_3194_ = lean_nat_add(v___x_3193_, v_size_3169_);
lean_dec(v___x_3193_);
v___x_3215_ = lean_nat_add(v___x_3019_, v_size_3181_);
if (lean_obj_tag(v_l_3185_) == 0)
{
lean_object* v_size_3225_; 
v_size_3225_ = lean_ctor_get(v_l_3185_, 0);
lean_inc(v_size_3225_);
v___y_3217_ = v_size_3225_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_unsigned_to_nat(0u);
v___y_3217_ = v___x_3226_;
goto v___jp_3216_;
}
v___jp_3195_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_nat_add(v___y_3196_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec(v___y_3196_);
lean_inc_ref(v_tree_3166_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 4, v_tree_3166_);
lean_ctor_set(v___x_3191_, 3, v_r_3186_);
lean_ctor_set(v___x_3191_, 2, v_v_3168_);
lean_ctor_set(v___x_3191_, 1, v_k_3167_);
lean_ctor_set(v___x_3191_, 0, v___x_3199_);
v___x_3201_ = v___x_3191_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_r_3186_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v_tree_3166_);
v___x_3201_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
v_isSharedCheck_3208_ = !lean_is_exclusive(v_tree_3166_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; lean_object* v_unused_3210_; lean_object* v_unused_3211_; lean_object* v_unused_3212_; lean_object* v_unused_3213_; 
v_unused_3209_ = lean_ctor_get(v_tree_3166_, 4);
lean_dec(v_unused_3209_);
v_unused_3210_ = lean_ctor_get(v_tree_3166_, 3);
lean_dec(v_unused_3210_);
v_unused_3211_ = lean_ctor_get(v_tree_3166_, 2);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v_tree_3166_, 1);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_tree_3166_, 0);
lean_dec(v_unused_3213_);
v___x_3203_ = v_tree_3166_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v_tree_3166_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v___x_3201_);
lean_ctor_set(v___x_3203_, 3, v___y_3197_);
lean_ctor_set(v___x_3203_, 2, v_v_3184_);
lean_ctor_set(v___x_3203_, 1, v_k_3183_);
lean_ctor_set(v___x_3203_, 0, v___x_3194_);
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_k_3183_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_v_3184_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v___y_3197_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v___x_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
v___jp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = lean_nat_add(v___x_3215_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec(v___x_3215_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_l_3185_);
lean_ctor_set(v___x_3163_, 3, v_l_3012_);
lean_ctor_set(v___x_3163_, 2, v_v_3011_);
lean_ctor_set(v___x_3163_, 1, v_k_3010_);
lean_ctor_set(v___x_3163_, 0, v___x_3218_);
v___x_3220_ = v___x_3163_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_k_3010_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_v_3011_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_l_3012_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_l_3185_);
v___x_3220_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_nat_add(v___x_3019_, v_size_3169_);
if (lean_obj_tag(v_r_3186_) == 0)
{
lean_object* v_size_3222_; 
v_size_3222_ = lean_ctor_get(v_r_3186_, 0);
lean_inc(v_size_3222_);
v___y_3196_ = v___x_3221_;
v___y_3197_ = v___x_3220_;
v___y_3198_ = v_size_3222_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_unsigned_to_nat(0u);
v___y_3196_ = v___x_3221_;
v___y_3197_ = v___x_3220_;
v___y_3198_ = v___x_3223_;
goto v___jp_3195_;
}
}
}
}
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3233_ = lean_nat_add(v___x_3019_, v_size_3009_);
lean_dec(v_size_3009_);
v___x_3234_ = lean_nat_add(v___x_3233_, v_size_3169_);
lean_dec(v___x_3233_);
v___x_3235_ = lean_nat_add(v___x_3019_, v_size_3169_);
v___x_3236_ = lean_nat_add(v___x_3235_, v_size_3182_);
lean_dec(v___x_3235_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_tree_3166_);
lean_ctor_set(v___x_3163_, 3, v_r_3013_);
lean_ctor_set(v___x_3163_, 2, v_v_3168_);
lean_ctor_set(v___x_3163_, 1, v_k_3167_);
lean_ctor_set(v___x_3163_, 0, v___x_3236_);
v___x_3238_ = v___x_3163_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3242_, 3, v_r_3013_);
lean_ctor_set(v_reuseFailAlloc_3242_, 4, v_tree_3166_);
v___x_3238_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___x_3238_);
lean_ctor_set(v___x_3179_, 0, v___x_3234_);
v___x_3240_ = v___x_3179_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_k_3010_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v_v_3011_);
lean_ctor_set(v_reuseFailAlloc_3241_, 3, v_l_3012_);
lean_ctor_set(v_reuseFailAlloc_3241_, 4, v___x_3238_);
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
else
{
if (lean_obj_tag(v_l_3012_) == 0)
{
lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3272_; 
lean_inc_ref(v_l_3012_);
lean_inc(v_v_3011_);
lean_inc(v_k_3010_);
lean_inc(v_size_3009_);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; lean_object* v_unused_3274_; lean_object* v_unused_3275_; lean_object* v_unused_3276_; lean_object* v_unused_3277_; 
v_unused_3273_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3273_);
v_unused_3274_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3274_);
v_unused_3275_ = lean_ctor_get(v_l_2829_, 2);
lean_dec(v_unused_3275_);
v_unused_3276_ = lean_ctor_get(v_l_2829_, 1);
lean_dec(v_unused_3276_);
v_unused_3277_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3277_);
v___x_3250_ = v_l_2829_;
v_isShared_3251_ = v_isSharedCheck_3272_;
goto v_resetjp_3249_;
}
else
{
lean_dec(v_l_2829_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3272_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
if (lean_obj_tag(v_r_3013_) == 0)
{
lean_object* v_k_3252_; lean_object* v_v_3253_; lean_object* v_size_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v_k_3252_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_k_3252_);
v_v_3253_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_v_3253_);
lean_dec_ref(v___x_3165_);
v_size_3254_ = lean_ctor_get(v_r_3013_, 0);
v___x_3255_ = lean_nat_add(v___x_3019_, v_size_3009_);
lean_dec(v_size_3009_);
v___x_3256_ = lean_nat_add(v___x_3019_, v_size_3254_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_tree_3166_);
lean_ctor_set(v___x_3163_, 3, v_r_3013_);
lean_ctor_set(v___x_3163_, 2, v_v_3253_);
lean_ctor_set(v___x_3163_, 1, v_k_3252_);
lean_ctor_set(v___x_3163_, 0, v___x_3256_);
v___x_3258_ = v___x_3163_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_k_3252_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_v_3253_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_r_3013_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v_tree_3166_);
v___x_3258_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3260_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 4, v___x_3258_);
lean_ctor_set(v___x_3250_, 0, v___x_3255_);
v___x_3260_ = v___x_3250_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_k_3010_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_v_3011_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v_l_3012_);
lean_ctor_set(v_reuseFailAlloc_3261_, 4, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_object* v_k_3263_; lean_object* v_v_3264_; lean_object* v___x_3265_; lean_object* v___x_3267_; 
lean_dec(v_size_3009_);
v_k_3263_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_k_3263_);
v_v_3264_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_v_3264_);
lean_dec_ref(v___x_3165_);
v___x_3265_ = lean_unsigned_to_nat(3u);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_r_3013_);
lean_ctor_set(v___x_3163_, 3, v_r_3013_);
lean_ctor_set(v___x_3163_, 2, v_v_3264_);
lean_ctor_set(v___x_3163_, 1, v_k_3263_);
lean_ctor_set(v___x_3163_, 0, v___x_3019_);
v___x_3267_ = v___x_3163_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_k_3263_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_v_3264_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_r_3013_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_r_3013_);
v___x_3267_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3269_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 4, v___x_3267_);
lean_ctor_set(v___x_3250_, 0, v___x_3265_);
v___x_3269_ = v___x_3250_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_k_3010_);
lean_ctor_set(v_reuseFailAlloc_3270_, 2, v_v_3011_);
lean_ctor_set(v_reuseFailAlloc_3270_, 3, v_l_3012_);
lean_ctor_set(v_reuseFailAlloc_3270_, 4, v___x_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3013_) == 0)
{
lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3302_; 
lean_inc(v_l_3012_);
lean_inc(v_v_3011_);
lean_inc(v_k_3010_);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; lean_object* v_unused_3307_; 
v_unused_3303_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_2829_, 2);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_l_2829_, 1);
lean_dec(v_unused_3306_);
v_unused_3307_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3307_);
v___x_3279_ = v_l_2829_;
v_isShared_3280_ = v_isSharedCheck_3302_;
goto v_resetjp_3278_;
}
else
{
lean_dec(v_l_2829_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3302_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v_k_3281_; lean_object* v_v_3282_; lean_object* v_k_3283_; lean_object* v_v_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3298_; 
v_k_3281_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_k_3281_);
v_v_3282_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_v_3282_);
lean_dec_ref(v___x_3165_);
v_k_3283_ = lean_ctor_get(v_r_3013_, 1);
v_v_3284_ = lean_ctor_get(v_r_3013_, 2);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_r_3013_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; lean_object* v_unused_3300_; lean_object* v_unused_3301_; 
v_unused_3299_ = lean_ctor_get(v_r_3013_, 4);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v_r_3013_, 3);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_r_3013_, 0);
lean_dec(v_unused_3301_);
v___x_3286_ = v_r_3013_;
v_isShared_3287_ = v_isSharedCheck_3298_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_v_3284_);
lean_inc(v_k_3283_);
lean_dec(v_r_3013_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3298_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = lean_unsigned_to_nat(3u);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v_l_3012_);
lean_ctor_set(v___x_3286_, 3, v_l_3012_);
lean_ctor_set(v___x_3286_, 2, v_v_3011_);
lean_ctor_set(v___x_3286_, 1, v_k_3010_);
lean_ctor_set(v___x_3286_, 0, v___x_3019_);
v___x_3290_ = v___x_3286_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_k_3010_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_v_3011_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_l_3012_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_l_3012_);
v___x_3290_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3292_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_l_3012_);
lean_ctor_set(v___x_3163_, 3, v_l_3012_);
lean_ctor_set(v___x_3163_, 2, v_v_3282_);
lean_ctor_set(v___x_3163_, 1, v_k_3281_);
lean_ctor_set(v___x_3163_, 0, v___x_3019_);
v___x_3292_ = v___x_3163_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_k_3281_);
lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_v_3282_);
lean_ctor_set(v_reuseFailAlloc_3296_, 3, v_l_3012_);
lean_ctor_set(v_reuseFailAlloc_3296_, 4, v_l_3012_);
v___x_3292_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3294_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 4, v___x_3292_);
lean_ctor_set(v___x_3279_, 3, v___x_3290_);
lean_ctor_set(v___x_3279_, 2, v_v_3284_);
lean_ctor_set(v___x_3279_, 1, v_k_3283_);
lean_ctor_set(v___x_3279_, 0, v___x_3288_);
v___x_3294_ = v___x_3279_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_k_3283_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_v_3284_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3295_, 4, v___x_3292_);
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
else
{
lean_object* v_k_3308_; lean_object* v_v_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v_k_3308_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_k_3308_);
v_v_3309_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_v_3309_);
lean_dec_ref(v___x_3165_);
v___x_3310_ = lean_unsigned_to_nat(2u);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v_r_3013_);
lean_ctor_set(v___x_3163_, 3, v_l_2829_);
lean_ctor_set(v___x_3163_, 2, v_v_3309_);
lean_ctor_set(v___x_3163_, 1, v_k_3308_);
lean_ctor_set(v___x_3163_, 0, v___x_3310_);
v___x_3312_ = v___x_3163_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_3308_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_3309_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_l_2829_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_r_3013_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
}
}
else
{
return v_l_2829_;
}
}
else
{
return v_r_2830_;
}
}
default: 
{
lean_object* v_impl_3320_; lean_object* v___x_3321_; 
v_impl_3320_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2825_, v_r_2830_);
v___x_3321_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3320_) == 0)
{
if (lean_obj_tag(v_l_2829_) == 0)
{
lean_object* v_size_3322_; lean_object* v_size_3323_; lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v_l_3326_; lean_object* v_r_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v_size_3322_ = lean_ctor_get(v_impl_3320_, 0);
v_size_3323_ = lean_ctor_get(v_l_2829_, 0);
v_k_3324_ = lean_ctor_get(v_l_2829_, 1);
v_v_3325_ = lean_ctor_get(v_l_2829_, 2);
v_l_3326_ = lean_ctor_get(v_l_2829_, 3);
v_r_3327_ = lean_ctor_get(v_l_2829_, 4);
lean_inc(v_r_3327_);
v___x_3328_ = lean_unsigned_to_nat(3u);
v___x_3329_ = lean_nat_mul(v___x_3328_, v_size_3322_);
v___x_3330_ = lean_nat_dec_lt(v___x_3329_, v_size_3323_);
lean_dec(v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_dec(v_r_3327_);
v___x_3331_ = lean_nat_add(v___x_3321_, v_size_3323_);
v___x_3332_ = lean_nat_add(v___x_3331_, v_size_3322_);
lean_dec(v___x_3331_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_impl_3320_);
lean_ctor_set(v___x_2832_, 0, v___x_3332_);
v___x_3334_ = v___x_2832_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_l_2829_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_impl_3320_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
else
{
lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3401_; 
lean_inc(v_l_3326_);
lean_inc(v_v_3325_);
lean_inc(v_k_3324_);
lean_inc(v_size_3323_);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; lean_object* v_unused_3405_; lean_object* v_unused_3406_; 
v_unused_3402_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_l_2829_, 2);
lean_dec(v_unused_3404_);
v_unused_3405_ = lean_ctor_get(v_l_2829_, 1);
lean_dec(v_unused_3405_);
v_unused_3406_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3406_);
v___x_3337_ = v_l_2829_;
v_isShared_3338_ = v_isSharedCheck_3401_;
goto v_resetjp_3336_;
}
else
{
lean_dec(v_l_2829_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3401_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_size_3339_; lean_object* v_size_3340_; lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_l_3343_; lean_object* v_r_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_size_3339_ = lean_ctor_get(v_l_3326_, 0);
v_size_3340_ = lean_ctor_get(v_r_3327_, 0);
v_k_3341_ = lean_ctor_get(v_r_3327_, 1);
v_v_3342_ = lean_ctor_get(v_r_3327_, 2);
v_l_3343_ = lean_ctor_get(v_r_3327_, 3);
v_r_3344_ = lean_ctor_get(v_r_3327_, 4);
v___x_3345_ = lean_unsigned_to_nat(2u);
v___x_3346_ = lean_nat_mul(v___x_3345_, v_size_3339_);
v___x_3347_ = lean_nat_dec_lt(v_size_3340_, v___x_3346_);
lean_dec(v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3376_; 
lean_inc(v_r_3344_);
lean_inc(v_l_3343_);
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_r_3327_);
if (v_isSharedCheck_3376_ == 0)
{
lean_object* v_unused_3377_; lean_object* v_unused_3378_; lean_object* v_unused_3379_; lean_object* v_unused_3380_; lean_object* v_unused_3381_; 
v_unused_3377_ = lean_ctor_get(v_r_3327_, 4);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_r_3327_, 3);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_r_3327_, 2);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_r_3327_, 1);
lean_dec(v_unused_3380_);
v_unused_3381_ = lean_ctor_get(v_r_3327_, 0);
lean_dec(v_unused_3381_);
v___x_3349_ = v_r_3327_;
v_isShared_3350_ = v_isSharedCheck_3376_;
goto v_resetjp_3348_;
}
else
{
lean_dec(v_r_3327_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3376_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___x_3364_; lean_object* v___y_3366_; 
v___x_3351_ = lean_nat_add(v___x_3321_, v_size_3323_);
lean_dec(v_size_3323_);
v___x_3352_ = lean_nat_add(v___x_3351_, v_size_3322_);
lean_dec(v___x_3351_);
v___x_3364_ = lean_nat_add(v___x_3321_, v_size_3339_);
if (lean_obj_tag(v_l_3343_) == 0)
{
lean_object* v_size_3374_; 
v_size_3374_ = lean_ctor_get(v_l_3343_, 0);
lean_inc(v_size_3374_);
v___y_3366_ = v_size_3374_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_unsigned_to_nat(0u);
v___y_3366_ = v___x_3375_;
goto v___jp_3365_;
}
v___jp_3353_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_nat_add(v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 4, v_impl_3320_);
lean_ctor_set(v___x_3349_, 3, v_r_3344_);
lean_ctor_set(v___x_3349_, 2, v_v_2828_);
lean_ctor_set(v___x_3349_, 1, v_k_2827_);
lean_ctor_set(v___x_3349_, 0, v___x_3357_);
v___x_3359_ = v___x_3349_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3344_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_impl_3320_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 4, v___x_3359_);
lean_ctor_set(v___x_3337_, 3, v___y_3354_);
lean_ctor_set(v___x_3337_, 2, v_v_3342_);
lean_ctor_set(v___x_3337_, 1, v_k_3341_);
lean_ctor_set(v___x_3337_, 0, v___x_3352_);
v___x_3361_ = v___x_3337_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___y_3354_);
lean_ctor_set(v_reuseFailAlloc_3362_, 4, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
v___jp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_nat_add(v___x_3364_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec(v___x_3364_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_l_3343_);
lean_ctor_set(v___x_2832_, 3, v_l_3326_);
lean_ctor_set(v___x_2832_, 2, v_v_3325_);
lean_ctor_set(v___x_2832_, 1, v_k_3324_);
lean_ctor_set(v___x_2832_, 0, v___x_3367_);
v___x_3369_ = v___x_2832_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_l_3326_);
lean_ctor_set(v_reuseFailAlloc_3373_, 4, v_l_3343_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_nat_add(v___x_3321_, v_size_3322_);
if (lean_obj_tag(v_r_3344_) == 0)
{
lean_object* v_size_3371_; 
v_size_3371_ = lean_ctor_get(v_r_3344_, 0);
lean_inc(v_size_3371_);
v___y_3354_ = v___x_3369_;
v___y_3355_ = v___x_3370_;
v___y_3356_ = v_size_3371_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_unsigned_to_nat(0u);
v___y_3354_ = v___x_3369_;
v___y_3355_ = v___x_3370_;
v___y_3356_ = v___x_3372_;
goto v___jp_3353_;
}
}
}
}
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
lean_del_object(v___x_2832_);
v___x_3382_ = lean_nat_add(v___x_3321_, v_size_3323_);
lean_dec(v_size_3323_);
v___x_3383_ = lean_nat_add(v___x_3382_, v_size_3322_);
lean_dec(v___x_3382_);
v___x_3384_ = lean_nat_add(v___x_3321_, v_size_3322_);
v___x_3385_ = lean_nat_add(v___x_3384_, v_size_3340_);
lean_dec(v___x_3384_);
lean_inc_ref(v_impl_3320_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 4, v_impl_3320_);
lean_ctor_set(v___x_3337_, 3, v_r_3327_);
lean_ctor_set(v___x_3337_, 2, v_v_2828_);
lean_ctor_set(v___x_3337_, 1, v_k_2827_);
lean_ctor_set(v___x_3337_, 0, v___x_3385_);
v___x_3387_ = v___x_3337_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3400_, 3, v_r_3327_);
lean_ctor_set(v_reuseFailAlloc_3400_, 4, v_impl_3320_);
v___x_3387_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_isSharedCheck_3394_ = !lean_is_exclusive(v_impl_3320_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; lean_object* v_unused_3399_; 
v_unused_3395_ = lean_ctor_get(v_impl_3320_, 4);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_impl_3320_, 3);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_impl_3320_, 2);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_impl_3320_, 1);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_impl_3320_, 0);
lean_dec(v_unused_3399_);
v___x_3389_ = v_impl_3320_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_dec(v_impl_3320_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 4, v___x_3387_);
lean_ctor_set(v___x_3389_, 3, v_l_3326_);
lean_ctor_set(v___x_3389_, 2, v_v_3325_);
lean_ctor_set(v___x_3389_, 1, v_k_3324_);
lean_ctor_set(v___x_3389_, 0, v___x_3383_);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_l_3326_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v___x_3387_);
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
}
}
}
else
{
lean_object* v_size_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v_size_3407_ = lean_ctor_get(v_impl_3320_, 0);
v___x_3408_ = lean_nat_add(v___x_3321_, v_size_3407_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_impl_3320_);
lean_ctor_set(v___x_2832_, 0, v___x_3408_);
v___x_3410_ = v___x_2832_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_l_2829_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v_impl_3320_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
else
{
if (lean_obj_tag(v_l_2829_) == 0)
{
lean_object* v_l_3412_; 
v_l_3412_ = lean_ctor_get(v_l_2829_, 3);
if (lean_obj_tag(v_l_3412_) == 0)
{
lean_object* v_r_3413_; 
lean_inc_ref(v_l_3412_);
v_r_3413_ = lean_ctor_get(v_l_2829_, 4);
lean_inc(v_r_3413_);
if (lean_obj_tag(v_r_3413_) == 0)
{
lean_object* v_size_3414_; lean_object* v_k_3415_; lean_object* v_v_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3429_; 
v_size_3414_ = lean_ctor_get(v_l_2829_, 0);
v_k_3415_ = lean_ctor_get(v_l_2829_, 1);
v_v_3416_ = lean_ctor_get(v_l_2829_, 2);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; lean_object* v_unused_3431_; 
v_unused_3430_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3431_);
v___x_3418_ = v_l_2829_;
v_isShared_3419_ = v_isSharedCheck_3429_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_v_3416_);
lean_inc(v_k_3415_);
lean_inc(v_size_3414_);
lean_dec(v_l_2829_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3429_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_size_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v_size_3420_ = lean_ctor_get(v_r_3413_, 0);
v___x_3421_ = lean_nat_add(v___x_3321_, v_size_3414_);
lean_dec(v_size_3414_);
v___x_3422_ = lean_nat_add(v___x_3321_, v_size_3420_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 4, v_impl_3320_);
lean_ctor_set(v___x_3418_, 3, v_r_3413_);
lean_ctor_set(v___x_3418_, 2, v_v_2828_);
lean_ctor_set(v___x_3418_, 1, v_k_2827_);
lean_ctor_set(v___x_3418_, 0, v___x_3422_);
v___x_3424_ = v___x_3418_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_r_3413_);
lean_ctor_set(v_reuseFailAlloc_3428_, 4, v_impl_3320_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v___x_3424_);
lean_ctor_set(v___x_2832_, 3, v_l_3412_);
lean_ctor_set(v___x_2832_, 2, v_v_3416_);
lean_ctor_set(v___x_2832_, 1, v_k_3415_);
lean_ctor_set(v___x_2832_, 0, v___x_3421_);
v___x_3426_ = v___x_2832_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_k_3415_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_v_3416_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3427_, 4, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
else
{
lean_object* v_k_3432_; lean_object* v_v_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3444_; 
v_k_3432_ = lean_ctor_get(v_l_2829_, 1);
v_v_3433_ = lean_ctor_get(v_l_2829_, 2);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; lean_object* v_unused_3446_; lean_object* v_unused_3447_; 
v_unused_3445_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3445_);
v_unused_3446_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3446_);
v_unused_3447_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3447_);
v___x_3435_ = v_l_2829_;
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_v_3433_);
lean_inc(v_k_3432_);
lean_dec(v_l_2829_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = lean_unsigned_to_nat(3u);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 3, v_r_3413_);
lean_ctor_set(v___x_3435_, 2, v_v_2828_);
lean_ctor_set(v___x_3435_, 1, v_k_2827_);
lean_ctor_set(v___x_3435_, 0, v___x_3321_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3443_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3443_, 3, v_r_3413_);
lean_ctor_set(v_reuseFailAlloc_3443_, 4, v_r_3413_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v___x_3439_);
lean_ctor_set(v___x_2832_, 3, v_l_3412_);
lean_ctor_set(v___x_2832_, 2, v_v_3433_);
lean_ctor_set(v___x_2832_, 1, v_k_3432_);
lean_ctor_set(v___x_2832_, 0, v___x_3437_);
v___x_3441_ = v___x_2832_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_k_3432_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_v_3433_);
lean_ctor_set(v_reuseFailAlloc_3442_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3442_, 4, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
else
{
lean_object* v_r_3448_; 
v_r_3448_ = lean_ctor_get(v_l_2829_, 4);
lean_inc(v_r_3448_);
if (lean_obj_tag(v_r_3448_) == 0)
{
lean_object* v_k_3449_; lean_object* v_v_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3473_; 
lean_inc(v_l_3412_);
v_k_3449_ = lean_ctor_get(v_l_2829_, 1);
v_v_3450_ = lean_ctor_get(v_l_2829_, 2);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_l_2829_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; lean_object* v_unused_3475_; lean_object* v_unused_3476_; 
v_unused_3474_ = lean_ctor_get(v_l_2829_, 4);
lean_dec(v_unused_3474_);
v_unused_3475_ = lean_ctor_get(v_l_2829_, 3);
lean_dec(v_unused_3475_);
v_unused_3476_ = lean_ctor_get(v_l_2829_, 0);
lean_dec(v_unused_3476_);
v___x_3452_ = v_l_2829_;
v_isShared_3453_ = v_isSharedCheck_3473_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_v_3450_);
lean_inc(v_k_3449_);
lean_dec(v_l_2829_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3473_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_k_3454_; lean_object* v_v_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3469_; 
v_k_3454_ = lean_ctor_get(v_r_3448_, 1);
v_v_3455_ = lean_ctor_get(v_r_3448_, 2);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_r_3448_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; lean_object* v_unused_3471_; lean_object* v_unused_3472_; 
v_unused_3470_ = lean_ctor_get(v_r_3448_, 4);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_r_3448_, 3);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_r_3448_, 0);
lean_dec(v_unused_3472_);
v___x_3457_ = v_r_3448_;
v_isShared_3458_ = v_isSharedCheck_3469_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_v_3455_);
lean_inc(v_k_3454_);
lean_dec(v_r_3448_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3469_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3459_ = lean_unsigned_to_nat(3u);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 4, v_l_3412_);
lean_ctor_set(v___x_3457_, 3, v_l_3412_);
lean_ctor_set(v___x_3457_, 2, v_v_3450_);
lean_ctor_set(v___x_3457_, 1, v_k_3449_);
lean_ctor_set(v___x_3457_, 0, v___x_3321_);
v___x_3461_ = v___x_3457_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_k_3449_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_v_3450_);
lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_l_3412_);
v___x_3461_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 4, v_l_3412_);
lean_ctor_set(v___x_3452_, 2, v_v_2828_);
lean_ctor_set(v___x_3452_, 1, v_k_2827_);
lean_ctor_set(v___x_3452_, 0, v___x_3321_);
v___x_3463_ = v___x_3452_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_l_3412_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_l_3412_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v___x_3463_);
lean_ctor_set(v___x_2832_, 3, v___x_3461_);
lean_ctor_set(v___x_2832_, 2, v_v_3455_);
lean_ctor_set(v___x_2832_, 1, v_k_3454_);
lean_ctor_set(v___x_2832_, 0, v___x_3459_);
v___x_3465_ = v___x_2832_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_k_3454_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_v_3455_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = lean_unsigned_to_nat(2u);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_r_3448_);
lean_ctor_set(v___x_2832_, 0, v___x_3477_);
v___x_3479_ = v___x_2832_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_l_2829_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_r_3448_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v___x_3482_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_l_2829_);
lean_ctor_set(v___x_2832_, 0, v___x_3321_);
v___x_3482_ = v___x_2832_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_l_2829_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_l_2829_);
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
}
}
}
else
{
return v_t_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3486_, lean_object* v_t_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3486_, v_t_3487_);
lean_dec(v_k_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3489_, lean_object* v_ps_3490_){
_start:
{
lean_object* v_importedEntries_3491_; lean_object* v_state_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
v_importedEntries_3491_ = lean_ctor_get(v_ps_3490_, 0);
v_state_3492_ = lean_ctor_get(v_ps_3490_, 1);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_ps_3490_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3494_ = v_ps_3490_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_state_3492_);
lean_inc(v_importedEntries_3491_);
lean_dec(v_ps_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3489_, v_state_3492_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 1, v___x_3496_);
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_importedEntries_3491_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3501_, lean_object* v_ps_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3501_, v_ps_3502_);
lean_dec(v_declName_3501_);
return v_res_3503_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___f_3547_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___x_3570_; lean_object* v_env_3571_; lean_object* v___x_3572_; 
lean_inc(v_declName_3507_);
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3547_, 0, v_declName_3507_);
v___x_3570_ = lean_st_ref_get(v___y_3513_);
v_env_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc_ref(v_env_3571_);
lean_dec(v___x_3570_);
v___x_3572_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3571_, v_declName_3507_);
lean_dec_ref(v_env_3571_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_dec(v_declName_3507_);
v___y_3549_ = v___y_3511_;
v___y_3550_ = v___y_3513_;
goto v___jp_3548_;
}
else
{
uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec_ref_known(v___x_3572_, 1);
lean_dec_ref(v___f_3547_);
v___x_3573_ = 0;
v___x_3574_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3575_ = l_Lean_MessageData_ofConstName(v_declName_3507_, v___x_3573_);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3578_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
return v___x_3579_;
}
v___jp_3515_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_mctx_3531_; lean_object* v_zetaDeltaFVarIds_3532_; lean_object* v_postponed_3533_; lean_object* v_diag_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3545_; 
v___x_3527_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_3528_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3528_, 0, v___y_3526_);
lean_ctor_set(v___x_3528_, 1, v___y_3525_);
lean_ctor_set(v___x_3528_, 2, v___y_3520_);
lean_ctor_set(v___x_3528_, 3, v___y_3523_);
lean_ctor_set(v___x_3528_, 4, v___y_3521_);
lean_ctor_set(v___x_3528_, 5, v___x_3527_);
lean_ctor_set(v___x_3528_, 6, v___y_3519_);
lean_ctor_set(v___x_3528_, 7, v___y_3522_);
lean_ctor_set(v___x_3528_, 8, v___y_3516_);
lean_ctor_set(v___x_3528_, 9, v___y_3524_);
v___x_3529_ = lean_st_ref_put(v___y_3518_, v___x_3528_);
v___x_3530_ = lean_st_ref_take(v___y_3517_);
v_mctx_3531_ = lean_ctor_get(v___x_3530_, 0);
v_zetaDeltaFVarIds_3532_ = lean_ctor_get(v___x_3530_, 2);
v_postponed_3533_ = lean_ctor_get(v___x_3530_, 3);
v_diag_3534_ = lean_ctor_get(v___x_3530_, 4);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v___x_3530_, 1);
lean_dec(v_unused_3546_);
v___x_3536_ = v___x_3530_;
v_isShared_3537_ = v_isSharedCheck_3545_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_diag_3534_);
lean_inc(v_postponed_3533_);
lean_inc(v_zetaDeltaFVarIds_3532_);
lean_inc(v_mctx_3531_);
lean_dec(v___x_3530_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3545_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 1, v___x_3539_);
v___x_3541_ = v___x_3536_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_mctx_3531_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_zetaDeltaFVarIds_3532_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_postponed_3533_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_diag_3534_);
v___x_3541_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_st_ref_put(v___y_3517_, v___x_3541_);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3538_);
return v___x_3543_;
}
}
}
v___jp_3548_:
{
lean_object* v___x_3551_; lean_object* v_env_3552_; lean_object* v_nextMacroScope_3553_; lean_object* v_ngen_3554_; lean_object* v_auxDeclNGen_3555_; lean_object* v_traceState_3556_; lean_object* v_recordedDeps_3557_; lean_object* v_messages_3558_; lean_object* v_infoState_3559_; lean_object* v_snapshotTasks_3560_; lean_object* v___x_3561_; lean_object* v_toEnvExtension_3562_; uint8_t v_logWrites_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3551_ = lean_st_ref_take(v___y_3550_);
v_env_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc_ref(v_env_3552_);
v_nextMacroScope_3553_ = lean_ctor_get(v___x_3551_, 1);
lean_inc(v_nextMacroScope_3553_);
v_ngen_3554_ = lean_ctor_get(v___x_3551_, 2);
lean_inc_ref(v_ngen_3554_);
v_auxDeclNGen_3555_ = lean_ctor_get(v___x_3551_, 3);
lean_inc_ref(v_auxDeclNGen_3555_);
v_traceState_3556_ = lean_ctor_get(v___x_3551_, 4);
lean_inc_ref(v_traceState_3556_);
v_recordedDeps_3557_ = lean_ctor_get(v___x_3551_, 6);
lean_inc_ref(v_recordedDeps_3557_);
v_messages_3558_ = lean_ctor_get(v___x_3551_, 7);
lean_inc_ref(v_messages_3558_);
v_infoState_3559_ = lean_ctor_get(v___x_3551_, 8);
lean_inc_ref(v_infoState_3559_);
v_snapshotTasks_3560_ = lean_ctor_get(v___x_3551_, 9);
lean_inc_ref(v_snapshotTasks_3560_);
lean_dec(v___x_3551_);
v___x_3561_ = l_Lean_docStringExt;
v_toEnvExtension_3562_ = lean_ctor_get(v___x_3561_, 0);
v_logWrites_3563_ = lean_ctor_get_uint8(v_toEnvExtension_3562_, sizeof(void*)*6);
v___x_3564_ = lean_box(2);
v___x_3565_ = lean_box(0);
v___x_3566_ = 1;
if (v_logWrites_3563_ == 0)
{
lean_object* v___x_3567_; 
lean_inc_ref(v_toEnvExtension_3562_);
v___x_3567_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3562_, v_env_3552_, v___f_3547_, v___x_3564_, v___x_3565_, v___x_3566_);
v___y_3516_ = v_infoState_3559_;
v___y_3517_ = v___y_3549_;
v___y_3518_ = v___y_3550_;
v___y_3519_ = v_recordedDeps_3557_;
v___y_3520_ = v_ngen_3554_;
v___y_3521_ = v_traceState_3556_;
v___y_3522_ = v_messages_3558_;
v___y_3523_ = v_auxDeclNGen_3555_;
v___y_3524_ = v_snapshotTasks_3560_;
v___y_3525_ = v_nextMacroScope_3553_;
v___y_3526_ = v___x_3567_;
goto v___jp_3515_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_inc_ref_n(v_toEnvExtension_3562_, 2);
v___x_3568_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3562_, v_env_3552_);
lean_dec_ref(v_env_3552_);
v___x_3569_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3562_, v___x_3568_, v___f_3547_, v___x_3564_, v___x_3565_, v___x_3566_);
v___y_3516_ = v_infoState_3559_;
v___y_3517_ = v___y_3549_;
v___y_3518_ = v___y_3550_;
v___y_3519_ = v_recordedDeps_3557_;
v___y_3520_ = v_ngen_3554_;
v___y_3521_ = v_traceState_3556_;
v___y_3522_ = v_messages_3558_;
v___y_3523_ = v_auxDeclNGen_3555_;
v___y_3524_ = v_snapshotTasks_3560_;
v___y_3525_ = v_nextMacroScope_3553_;
v___y_3526_ = v___x_3569_;
goto v___jp_3515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3588_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3594_ = l_Lean_stringToMessageData(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3597_ = l_Lean_stringToMessageData(v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_env_3610_; lean_object* v_ref_3611_; uint8_t v___x_3612_; lean_object* v___x_3613_; 
v___x_3609_ = lean_st_ref_get(v_a_3607_);
v_env_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc_ref(v_env_3610_);
lean_dec(v___x_3609_);
v_ref_3611_ = lean_ctor_get(v_a_3606_, 2);
v___x_3612_ = 1;
lean_inc(v_declName_3601_);
v___x_3613_ = l_Lean_findInternalDocString_x3f(v_env_3610_, v_declName_3601_, v___x_3612_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3615_; 
v_val_3615_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v_a_3614_, 1);
if (lean_obj_tag(v_val_3615_) == 0)
{
lean_object* v_val_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3637_; 
v_val_3616_ = lean_ctor_get(v_val_3615_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_val_3615_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3618_ = v_val_3615_;
v_isShared_3619_ = v_isSharedCheck_3637_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_val_3616_);
lean_dec(v_val_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3637_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_removeBuiltinDocString(v_declName_3601_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3620_, 1);
lean_del_object(v___x_3618_);
lean_inc(v_declName_3601_);
v___x_3621_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref_known(v___x_3621_, 1);
v___x_3622_ = l_Lean_addVersoDocStringFromString(v_declName_3601_, v_val_3616_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
return v___x_3622_;
}
else
{
lean_dec(v_val_3616_);
lean_dec(v_declName_3601_);
return v___x_3621_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v_val_3616_);
lean_dec(v_declName_3601_);
v_a_3623_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3625_ = v___x_3620_;
v_isShared_3626_ = v_isSharedCheck_3636_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3620_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3636_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3627_ = lean_io_error_to_string(v_a_3623_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 3);
lean_ctor_set(v___x_3618_, 0, v___x_3627_);
v___x_3629_ = v___x_3618_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3630_ = l_Lean_MessageData_ofFormat(v___x_3629_);
lean_inc(v_ref_3611_);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_ref_3611_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3631_);
v___x_3633_ = v___x_3625_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
else
{
lean_object* v___x_3638_; uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec(v_val_3615_);
v___x_3638_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3639_ = 0;
v___x_3640_ = l_Lean_MessageData_ofConstName(v_declName_3601_, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3638_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3643_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
return v___x_3644_;
}
}
else
{
lean_object* v___x_3645_; uint8_t v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec(v_a_3614_);
v___x_3645_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3646_ = 0;
v___x_3647_ = l_Lean_MessageData_ofConstName(v_declName_3601_, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3645_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3650_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
return v___x_3651_;
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_declName_3601_);
v_a_3652_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3654_ = v___x_3613_;
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3613_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3656_ = lean_io_error_to_string(v_a_3652_);
v___x_3657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
v___x_3658_ = l_Lean_MessageData_ofFormat(v___x_3657_);
lean_inc(v_ref_3611_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_ref_3611_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3659_);
v___x_3661_ = v___x_3654_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_makeDocStringVerso(v_declName_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3673_, lean_object* v_k_3674_, lean_object* v_t_3675_, lean_object* v_h_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3674_, v_t_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3678_, lean_object* v_k_3679_, lean_object* v_t_3680_, lean_object* v_h_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3678_, v_k_3679_, v_t_3680_, v_h_3681_);
lean_dec(v_k_3679_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3683_, lean_object* v_binders_3684_, lean_object* v_docComment_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
uint8_t v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = l_Lean_isVersoDocComment(v_docComment_3685_);
v___x_3694_ = l_Lean_addDocStringOf(v___x_3693_, v_declName_3683_, v_binders_3684_, v_docComment_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3695_, lean_object* v_binders_3696_, lean_object* v_docComment_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_addDocString(v_declName_3695_, v_binders_3696_, v_docComment_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
lean_dec(v_a_3703_);
lean_dec_ref(v_a_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_a_3700_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3706_, lean_object* v_binders_3707_, lean_object* v_docString_x3f_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3708_) == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec(v_binders_3707_);
lean_dec(v_declName_3706_);
v___x_3716_ = lean_box(0);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
else
{
lean_object* v_val_3718_; lean_object* v___x_3719_; 
v_val_3718_ = lean_ctor_get(v_docString_x3f_3708_, 0);
lean_inc(v_val_3718_);
lean_dec_ref_known(v_docString_x3f_3708_, 1);
v___x_3719_ = l_Lean_addDocString(v_declName_3706_, v_binders_3707_, v_val_3718_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
return v___x_3719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3720_, lean_object* v_binders_3721_, lean_object* v_docString_x3f_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_addDocString_x27(v_declName_3720_, v_binders_3721_, v_docString_x3f_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; lean_object* v_nextMacroScope_3736_; lean_object* v_ngen_3737_; lean_object* v_auxDeclNGen_3738_; lean_object* v_traceState_3739_; lean_object* v_recordedDeps_3740_; lean_object* v_messages_3741_; lean_object* v_infoState_3742_; lean_object* v_snapshotTasks_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3769_; 
v___x_3735_ = lean_st_ref_take(v___y_3733_);
v_nextMacroScope_3736_ = lean_ctor_get(v___x_3735_, 1);
v_ngen_3737_ = lean_ctor_get(v___x_3735_, 2);
v_auxDeclNGen_3738_ = lean_ctor_get(v___x_3735_, 3);
v_traceState_3739_ = lean_ctor_get(v___x_3735_, 4);
v_recordedDeps_3740_ = lean_ctor_get(v___x_3735_, 6);
v_messages_3741_ = lean_ctor_get(v___x_3735_, 7);
v_infoState_3742_ = lean_ctor_get(v___x_3735_, 8);
v_snapshotTasks_3743_ = lean_ctor_get(v___x_3735_, 9);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; lean_object* v_unused_3771_; 
v_unused_3770_ = lean_ctor_get(v___x_3735_, 5);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3771_);
v___x_3745_ = v___x_3735_;
v_isShared_3746_ = v_isSharedCheck_3769_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_snapshotTasks_3743_);
lean_inc(v_infoState_3742_);
lean_inc(v_messages_3741_);
lean_inc(v_recordedDeps_3740_);
lean_inc(v_traceState_3739_);
lean_inc(v_auxDeclNGen_3738_);
lean_inc(v_ngen_3737_);
lean_inc(v_nextMacroScope_3736_);
lean_dec(v___x_3735_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3769_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 5, v___x_3747_);
lean_ctor_set(v___x_3745_, 0, v_env_3731_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_env_3731_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_nextMacroScope_3736_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v_ngen_3737_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_auxDeclNGen_3738_);
lean_ctor_set(v_reuseFailAlloc_3768_, 4, v_traceState_3739_);
lean_ctor_set(v_reuseFailAlloc_3768_, 5, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3768_, 6, v_recordedDeps_3740_);
lean_ctor_set(v_reuseFailAlloc_3768_, 7, v_messages_3741_);
lean_ctor_set(v_reuseFailAlloc_3768_, 8, v_infoState_3742_);
lean_ctor_set(v_reuseFailAlloc_3768_, 9, v_snapshotTasks_3743_);
v___x_3749_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v_mctx_3752_; lean_object* v_zetaDeltaFVarIds_3753_; lean_object* v_postponed_3754_; lean_object* v_diag_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3766_; 
v___x_3750_ = lean_st_ref_put(v___y_3733_, v___x_3749_);
v___x_3751_ = lean_st_ref_take(v___y_3732_);
v_mctx_3752_ = lean_ctor_get(v___x_3751_, 0);
v_zetaDeltaFVarIds_3753_ = lean_ctor_get(v___x_3751_, 2);
v_postponed_3754_ = lean_ctor_get(v___x_3751_, 3);
v_diag_3755_ = lean_ctor_get(v___x_3751_, 4);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3766_ == 0)
{
lean_object* v_unused_3767_; 
v_unused_3767_ = lean_ctor_get(v___x_3751_, 1);
lean_dec(v_unused_3767_);
v___x_3757_ = v___x_3751_;
v_isShared_3758_ = v_isSharedCheck_3766_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_diag_3755_);
lean_inc(v_postponed_3754_);
lean_inc(v_zetaDeltaFVarIds_3753_);
lean_inc(v_mctx_3752_);
lean_dec(v___x_3751_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3766_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
v___x_3759_ = lean_box(0);
v___x_3760_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 1, v___x_3760_);
v___x_3762_ = v___x_3757_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_mctx_3752_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3765_, 2, v_zetaDeltaFVarIds_3753_);
lean_ctor_set(v_reuseFailAlloc_3765_, 3, v_postponed_3754_);
lean_ctor_set(v_reuseFailAlloc_3765_, 4, v_diag_3755_);
v___x_3762_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_st_ref_put(v___y_3732_, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3759_);
return v___x_3764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec(v___y_3773_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3777_, uint8_t v___x_3778_, lean_object* v_as_3779_, size_t v_i_3780_, size_t v_stop_3781_, lean_object* v_b_3782_){
_start:
{
lean_object* v___y_3784_; uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_eq(v_i_3780_, v_stop_3781_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v_index_3790_; lean_object* v_sourceString_3791_; lean_object* v_imports_3792_; lean_object* v_currNamespace_3793_; lean_object* v_openDecls_3794_; lean_object* v_options_3795_; lean_object* v_check_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3814_; 
v___x_3789_ = lean_array_uget(v_as_3779_, v_i_3780_);
v_index_3790_ = lean_ctor_get(v___x_3789_, 1);
v_sourceString_3791_ = lean_ctor_get(v___x_3789_, 2);
v_imports_3792_ = lean_ctor_get(v___x_3789_, 3);
v_currNamespace_3793_ = lean_ctor_get(v___x_3789_, 4);
v_openDecls_3794_ = lean_ctor_get(v___x_3789_, 5);
v_options_3795_ = lean_ctor_get(v___x_3789_, 6);
v_check_3796_ = lean_ctor_get(v___x_3789_, 7);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; 
v_unused_3815_ = lean_ctor_get(v___x_3789_, 0);
lean_dec(v_unused_3815_);
v___x_3798_ = v___x_3789_;
v_isShared_3799_ = v_isSharedCheck_3814_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_check_3796_);
lean_inc(v_options_3795_);
lean_inc(v_openDecls_3794_);
lean_inc(v_currNamespace_3793_);
lean_inc(v_imports_3792_);
lean_inc(v_sourceString_3791_);
lean_inc(v_index_3790_);
lean_dec(v___x_3789_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3814_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3800_; lean_object* v_toEnvExtension_3801_; lean_object* v_addEntryFn_3802_; lean_object* v_asyncMode_3803_; uint8_t v_logWrites_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3800_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3801_ = lean_ctor_get(v___x_3800_, 0);
v_addEntryFn_3802_ = lean_ctor_get(v___x_3800_, 3);
v_asyncMode_3803_ = lean_ctor_get(v_toEnvExtension_3801_, 2);
v_logWrites_3804_ = lean_ctor_get_uint8(v_toEnvExtension_3801_, sizeof(void*)*6);
lean_inc(v_n_3777_);
v___x_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3805_, 0, v_n_3777_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v___x_3805_);
v___x_3807_ = v___x_3798_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_index_3790_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_sourceString_3791_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_imports_3792_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_currNamespace_3793_);
lean_ctor_set(v_reuseFailAlloc_3813_, 5, v_openDecls_3794_);
lean_ctor_set(v_reuseFailAlloc_3813_, 6, v_options_3795_);
lean_ctor_set(v_reuseFailAlloc_3813_, 7, v_check_3796_);
v___x_3807_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___f_3808_; lean_object* v___x_3809_; 
lean_inc(v_addEntryFn_3802_);
v___f_3808_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_3808_, 0, v_addEntryFn_3802_);
lean_closure_set(v___f_3808_, 1, v___x_3807_);
v___x_3809_ = lean_box(0);
if (v_logWrites_3804_ == 0)
{
lean_object* v___x_3810_; 
lean_inc_ref(v_toEnvExtension_3801_);
v___x_3810_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3801_, v_b_3782_, v___f_3808_, v_asyncMode_3803_, v___x_3809_, v___x_3778_);
v___y_3784_ = v___x_3810_;
goto v___jp_3783_;
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_inc_ref_n(v_toEnvExtension_3801_, 2);
v___x_3811_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3801_, v_b_3782_);
lean_dec_ref(v_b_3782_);
v___x_3812_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3801_, v___x_3811_, v___f_3808_, v_asyncMode_3803_, v___x_3809_, v___x_3778_);
v___y_3784_ = v___x_3812_;
goto v___jp_3783_;
}
}
}
}
else
{
lean_dec(v_n_3777_);
return v_b_3782_;
}
v___jp_3783_:
{
size_t v___x_3785_; size_t v___x_3786_; 
v___x_3785_ = ((size_t)1ULL);
v___x_3786_ = lean_usize_add(v_i_3780_, v___x_3785_);
v_i_3780_ = v___x_3786_;
v_b_3782_ = v___y_3784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3816_, lean_object* v___x_3817_, lean_object* v_as_3818_, lean_object* v_i_3819_, lean_object* v_stop_3820_, lean_object* v_b_3821_){
_start:
{
uint8_t v___x_1371__boxed_3822_; size_t v_i_boxed_3823_; size_t v_stop_boxed_3824_; lean_object* v_res_3825_; 
v___x_1371__boxed_3822_ = lean_unbox(v___x_3817_);
v_i_boxed_3823_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_stop_boxed_3824_ = lean_unbox_usize(v_stop_3820_);
lean_dec(v_stop_3820_);
v_res_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3816_, v___x_1371__boxed_3822_, v_as_3818_, v_i_boxed_3823_, v_stop_boxed_3824_, v_b_3821_);
lean_dec_ref(v_as_3818_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3826_, lean_object* v_deferred_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; lean_object* v_env_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3835_ = lean_st_ref_get(v___y_3833_);
v_env_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc_ref(v_env_3836_);
lean_dec(v___x_3835_);
v___x_3837_ = l_Lean_getMainModuleDoc(v_env_3836_);
v___x_3838_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3837_);
lean_dec_ref(v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_dec_ref(v_docs_3826_);
v___x_3839_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3840_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3839_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; lean_object* v_env_3842_; lean_object* v___x_3843_; lean_object* v_size_3844_; lean_object* v___x_3845_; lean_object* v_env_3846_; lean_object* v___x_3847_; 
v___x_3841_ = lean_st_ref_get(v___y_3833_);
v_env_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc_ref(v_env_3842_);
lean_dec(v___x_3841_);
v___x_3843_ = l_Lean_getMainVersoModuleDocs(v_env_3842_);
v_size_3844_ = lean_ctor_get(v___x_3843_, 2);
lean_inc(v_size_3844_);
lean_dec_ref(v___x_3843_);
v___x_3845_ = lean_st_ref_get(v___y_3833_);
v_env_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc_ref(v_env_3846_);
lean_dec(v___x_3845_);
v___x_3847_ = l_Lean_addVersoModuleDocSnippet(v_env_3846_, v_docs_3826_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_dec(v_size_3844_);
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_3850_ = l_Lean_stringToMessageData(v_a_3848_);
v___x_3851_ = l_Lean_indentD(v___x_3850_);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3852_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
return v___x_3853_;
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v_a_3854_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_array_get_size(v_deferred_3827_);
v___x_3857_ = lean_nat_dec_lt(v___x_3855_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; 
lean_dec(v_size_3844_);
v___x_3858_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3854_, v___y_3831_, v___y_3833_);
return v___x_3858_;
}
else
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3859_ = ((size_t)0ULL);
v___x_3860_ = lean_usize_of_nat(v___x_3856_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3844_, v___x_3838_, v_deferred_3827_, v___x_3859_, v___x_3860_, v_a_3854_);
v___x_3862_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3861_, v___y_3831_, v___y_3833_);
return v___x_3862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3863_, lean_object* v_deferred_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3863_, v_deferred_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec_ref(v_deferred_3864_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3873_, lean_object* v_doc_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_versoModDocString(v_range_3873_, v_doc_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v_fst_3884_; lean_object* v_snd_3885_; lean_object* v___x_3886_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v_fst_3884_ = lean_ctor_get(v_a_3883_, 0);
lean_inc(v_fst_3884_);
v_snd_3885_ = lean_ctor_get(v_a_3883_, 1);
lean_inc(v_snd_3885_);
lean_dec(v_a_3883_);
v___x_3886_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3884_, v_snd_3885_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
lean_dec(v_snd_3885_);
return v___x_3886_;
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_a_3887_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3882_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3882_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
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
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3895_, lean_object* v_doc_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_addVersoModDocString(v_range_3895_, v_doc_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_doc_3896_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3905_, v___y_3909_, v___y_3911_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
return v_res_3922_;
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
