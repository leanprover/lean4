// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: import Lean.DocString import Lean.DocString.Add import Lean.Elab.DocString public import Lean.Elab.Command public import Lean.Parser.Tactic.Doc
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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_isVersoDocComment(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_parseVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_Doc_elabBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Doc_joinInlines(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_withRendererFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object*);
lean_object* l_Lean_Doc_joinBlocks(lean_object*);
lean_object* l_Lean_Doc_prefixListLines(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Doc_prefixLines(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_MarkdownM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_withExprHover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
extern lean_object* l_Lean_Parser_parserExtension;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__0_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__1_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__3_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__3_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__12_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__9_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__9_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__10_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__13;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__15 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__15_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__16 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__16_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__17 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__9(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__1_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic_extension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 145, 122, 23, 135, 199, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Malformed tactic extension command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Missing documentation comment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed `register_tactic_tag` command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 185, 128, 48, 210, 24, 186)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " — \""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Displays all available tactic tags, with documentation."};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__13(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__10));
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = lean_mk_empty_array_with_capacity(v___x_29_);
v___x_31_ = lean_array_push(v___x_30_, v___x_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed(lean_object* v_x_36_, lean_object* v_x_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v_x_36_, v_x_37_, v_a_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0___boxed(lean_object* v_x_45_, lean_object* v_sz_46_, lean_object* v___x_47_, lean_object* v_content_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
size_t v_sz_boxed_53_; size_t v___x_6052__boxed_54_; lean_object* v_res_55_; 
v_sz_boxed_53_ = lean_unbox_usize(v_sz_46_);
lean_dec(v_sz_46_);
v___x_6052__boxed_54_ = lean_unbox_usize(v___x_47_);
lean_dec(v___x_47_);
v_res_55_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(v_x_45_, v_sz_boxed_53_, v___x_6052__boxed_54_, v_content_48_, v___y_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_pieces_63_; lean_object* v_pieces_67_; 
switch(lean_obj_tag(v_x_57_))
{
case 0:
{
lean_object* v_string_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec_ref(v_x_56_);
v_string_70_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_70_);
lean_dec_ref_known(v_x_57_, 1);
v___x_71_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_70_);
lean_dec_ref(v_string_70_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_mk_empty_array_with_capacity(v___x_72_);
v___x_74_ = lean_array_push(v___x_73_, v___x_71_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
case 1:
{
lean_object* v_content_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_127_; 
v_content_76_ = lean_ctor_get(v_x_57_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_127_ == 0)
{
v___x_78_ = v_x_57_;
v_isShared_79_ = v_isSharedCheck_127_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_content_76_);
lean_dec(v_x_57_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_127_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 9);
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_content_76_);
v___x_81_ = v_reuseFailAlloc_126_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; lean_object* v_snd_83_; lean_object* v_fst_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v_pieces_88_; uint8_t v_inEmph_96_; uint8_t v_inBold_97_; uint8_t v_inLink_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_125_; 
v___x_82_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_81_);
v_snd_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_snd_83_);
v_fst_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_fst_84_);
lean_dec_ref(v___x_82_);
v_fst_85_ = lean_ctor_get(v_snd_83_, 0);
lean_inc(v_fst_85_);
v_snd_86_ = lean_ctor_get(v_snd_83_, 1);
lean_inc(v_snd_86_);
lean_dec(v_snd_83_);
v_inEmph_96_ = lean_ctor_get_uint8(v_x_56_, 0);
v_inBold_97_ = lean_ctor_get_uint8(v_x_56_, 1);
v_inLink_98_ = lean_ctor_get_uint8(v_x_56_, 2);
v_isSharedCheck_125_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_125_ == 0)
{
v___x_100_ = v_x_56_;
v_isShared_101_ = v_isSharedCheck_125_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_x_56_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_125_;
goto v_resetjp_99_;
}
v___jp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_89_ = lean_string_utf8_byte_size(v_snd_86_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_nat_dec_eq(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_array_push(v___x_93_, v_snd_86_);
v___x_95_ = lean_array_push(v_pieces_88_, v___x_94_);
v_pieces_67_ = v___x_95_;
goto v___jp_66_;
}
else
{
lean_dec(v_snd_86_);
v_pieces_67_ = v_pieces_88_;
goto v___jp_66_;
}
}
v_resetjp_99_:
{
uint8_t v___x_102_; lean_object* v___x_104_; 
v___x_102_ = 1;
if (v_isShared_101_ == 0)
{
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, 1, v_inBold_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, 2, v_inLink_98_);
v___x_104_ = v_reuseFailAlloc_124_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
lean_ctor_set_uint8(v___x_104_, 0, v___x_102_);
v___x_105_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_104_, v_fst_85_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_pieces_108_; lean_object* v_pieces_113_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2));
v___x_118_ = lean_string_utf8_byte_size(v_fst_84_);
v___x_119_ = lean_nat_dec_eq(v___x_118_, v___x_116_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_array_push(v___x_121_, v_fst_84_);
v___x_123_ = lean_array_push(v___x_117_, v___x_122_);
v_pieces_113_ = v___x_123_;
goto v___jp_112_;
}
else
{
lean_dec(v_fst_84_);
v_pieces_113_ = v___x_117_;
goto v___jp_112_;
}
v___jp_107_:
{
lean_object* v___x_109_; 
v___x_109_ = lean_array_push(v_pieces_108_, v_a_106_);
if (v_inEmph_96_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__1));
v___x_111_ = lean_array_push(v___x_109_, v___x_110_);
v_pieces_88_ = v___x_111_;
goto v___jp_87_;
}
else
{
v_pieces_88_ = v___x_109_;
goto v___jp_87_;
}
}
v___jp_112_:
{
if (v_inEmph_96_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__1));
v___x_115_ = lean_array_push(v_pieces_113_, v___x_114_);
v_pieces_108_ = v___x_115_;
goto v___jp_107_;
}
else
{
v_pieces_108_ = v_pieces_113_;
goto v___jp_107_;
}
}
}
else
{
lean_dec(v_snd_86_);
lean_dec(v_fst_84_);
return v___x_105_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_179_; 
v_content_128_ = lean_ctor_get(v_x_57_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_179_ == 0)
{
v___x_130_ = v_x_57_;
v_isShared_131_ = v_isSharedCheck_179_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_content_128_);
lean_dec(v_x_57_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_179_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 9);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_content_128_);
v___x_133_ = v_reuseFailAlloc_178_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v_snd_135_; lean_object* v_fst_136_; lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v_pieces_140_; uint8_t v_inEmph_148_; uint8_t v_inBold_149_; uint8_t v_inLink_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_177_; 
v___x_134_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_133_);
v_snd_135_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_snd_135_);
v_fst_136_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_fst_136_);
lean_dec_ref(v___x_134_);
v_fst_137_ = lean_ctor_get(v_snd_135_, 0);
lean_inc(v_fst_137_);
v_snd_138_ = lean_ctor_get(v_snd_135_, 1);
lean_inc(v_snd_138_);
lean_dec(v_snd_135_);
v_inEmph_148_ = lean_ctor_get_uint8(v_x_56_, 0);
v_inBold_149_ = lean_ctor_get_uint8(v_x_56_, 1);
v_inLink_150_ = lean_ctor_get_uint8(v_x_56_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_177_ == 0)
{
v___x_152_ = v_x_56_;
v_isShared_153_ = v_isSharedCheck_177_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_x_56_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_177_;
goto v_resetjp_151_;
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_string_utf8_byte_size(v_snd_138_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_nat_dec_eq(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_146_ = lean_array_push(v___x_145_, v_snd_138_);
v___x_147_ = lean_array_push(v_pieces_140_, v___x_146_);
v_pieces_63_ = v___x_147_;
goto v___jp_62_;
}
else
{
lean_dec(v_snd_138_);
v_pieces_63_ = v_pieces_140_;
goto v___jp_62_;
}
}
v_resetjp_151_:
{
uint8_t v___x_154_; lean_object* v___x_156_; 
v___x_154_ = 1;
if (v_isShared_153_ == 0)
{
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, 0, v_inEmph_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, 2, v_inLink_150_);
v___x_156_ = v_reuseFailAlloc_176_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
lean_ctor_set_uint8(v___x_156_, 1, v___x_154_);
v___x_157_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_156_, v_fst_137_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v_pieces_160_; lean_object* v_pieces_165_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2));
v___x_170_ = lean_string_utf8_byte_size(v_fst_136_);
v___x_171_ = lean_nat_dec_eq(v___x_170_, v___x_168_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_array_push(v___x_173_, v_fst_136_);
v___x_175_ = lean_array_push(v___x_169_, v___x_174_);
v_pieces_165_ = v___x_175_;
goto v___jp_164_;
}
else
{
lean_dec(v_fst_136_);
v_pieces_165_ = v___x_169_;
goto v___jp_164_;
}
v___jp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = lean_array_push(v_pieces_160_, v_a_158_);
if (v_inBold_149_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__4));
v___x_163_ = lean_array_push(v___x_161_, v___x_162_);
v_pieces_140_ = v___x_163_;
goto v___jp_139_;
}
else
{
v_pieces_140_ = v___x_161_;
goto v___jp_139_;
}
}
v___jp_164_:
{
if (v_inBold_149_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__4));
v___x_167_ = lean_array_push(v_pieces_165_, v___x_166_);
v_pieces_160_ = v___x_167_;
goto v___jp_159_;
}
else
{
v_pieces_160_ = v_pieces_165_;
goto v___jp_159_;
}
}
}
else
{
lean_dec(v_snd_138_);
lean_dec(v_fst_136_);
return v___x_157_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec_ref(v_x_56_);
v_string_180_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_180_);
lean_dec_ref_known(v_x_57_, 1);
v___x_181_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_180_);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_mk_empty_array_with_capacity(v___x_182_);
v___x_184_ = lean_array_push(v___x_183_, v___x_181_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
case 4:
{
uint8_t v_mode_186_; 
lean_dec_ref(v_x_56_);
v_mode_186_ = lean_ctor_get_uint8(v_x_57_, sizeof(void*)*1);
if (v_mode_186_ == 0)
{
lean_object* v_string_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_string_187_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_187_);
lean_dec_ref_known(v_x_57_, 1);
v___x_188_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__5));
v___x_189_ = lean_string_append(v___x_188_, v_string_187_);
lean_dec_ref(v_string_187_);
v___x_190_ = lean_string_append(v___x_189_, v___x_188_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_mk_empty_array_with_capacity(v___x_191_);
v___x_193_ = lean_array_push(v___x_192_, v___x_190_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_string_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_string_195_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_195_);
lean_dec_ref_known(v_x_57_, 1);
v___x_196_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__6));
v___x_197_ = lean_string_append(v___x_196_, v_string_195_);
lean_dec_ref(v_string_195_);
v___x_198_ = lean_string_append(v___x_197_, v___x_196_);
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_mk_empty_array_with_capacity(v___x_199_);
v___x_201_ = lean_array_push(v___x_200_, v___x_198_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
case 5:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref_known(v_x_57_, 1);
lean_dec_ref(v_x_56_);
v___x_203_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__8));
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
case 6:
{
uint8_t v_inLink_205_; 
v_inLink_205_ = lean_ctor_get_uint8(v_x_56_, 2);
if (v_inLink_205_ == 0)
{
lean_object* v_content_206_; lean_object* v_url_207_; uint8_t v_inEmph_208_; uint8_t v_inBold_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_238_; 
v_content_206_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_content_206_);
v_url_207_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_url_207_);
lean_dec_ref_known(v_x_57_, 2);
v_inEmph_208_ = lean_ctor_get_uint8(v_x_56_, 0);
v_inBold_209_ = lean_ctor_get_uint8(v_x_56_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_238_ == 0)
{
v___x_211_ = v_x_56_;
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
else
{
lean_dec(v_x_56_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint8_t v___x_213_; lean_object* v___x_215_; 
v___x_213_ = 1;
if (v_isShared_212_ == 0)
{
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 0, v_inEmph_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 1, v_inBold_209_);
v___x_215_ = v_reuseFailAlloc_237_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_ctor_set_uint8(v___x_215_, 2, v___x_213_);
v___x_216_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_216_, 0, v_content_206_);
v___x_217_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_215_, v___x_216_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_236_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_236_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_236_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_236_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_mk_empty_array_with_capacity(v___x_222_);
v___x_224_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__11));
v___x_225_ = lean_string_append(v___x_224_, v_url_207_);
lean_dec_ref(v_url_207_);
v___x_226_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__12));
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
v___x_228_ = lean_array_push(v___x_223_, v___x_227_);
v___x_229_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__13);
v___x_230_ = lean_array_push(v___x_229_, v_a_218_);
v___x_231_ = lean_array_push(v___x_230_, v___x_228_);
v___x_232_ = l_Lean_Doc_joinInlines(v___x_231_);
lean_dec_ref(v___x_231_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_232_);
v___x_234_ = v___x_220_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_dec_ref(v_url_207_);
return v___x_217_;
}
}
}
}
else
{
lean_object* v_content_239_; size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; 
v_content_239_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_content_239_);
lean_dec_ref_known(v_x_57_, 2);
v_sz_240_ = lean_array_size(v_content_239_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_56_, v_sz_240_, v___x_241_, v_content_239_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = l_Lean_Doc_joinInlines(v_a_243_);
lean_dec(v_a_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_242_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_242_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
case 7:
{
lean_object* v_name_260_; lean_object* v_content_261_; size_t v_sz_262_; size_t v___x_263_; lean_object* v___x_264_; 
v_name_260_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_name_260_);
v_content_261_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_content_261_);
lean_dec_ref_known(v_x_57_, 2);
v_sz_262_ = lean_array_size(v_content_261_);
v___x_263_ = ((size_t)0ULL);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_56_, v_sz_262_, v___x_263_, v_content_261_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__14));
v___x_267_ = l_Lean_Doc_joinInlines(v_a_265_);
lean_dec(v_a_265_);
v___x_268_ = lean_array_to_list(v___x_267_);
v___x_269_ = l_String_intercalate(v___x_266_, v___x_268_);
lean_inc_ref(v_name_260_);
v___x_270_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(v_name_260_, v___x_269_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_284_; 
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_285_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_274_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__15));
v___x_275_ = lean_string_append(v___x_274_, v_name_260_);
lean_dec_ref(v_name_260_);
v___x_276_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__16));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_push(v___x_279_, v___x_277_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_280_);
v___x_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_name_260_);
v_a_286_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_270_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_270_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_name_260_);
v_a_294_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_264_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_264_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
case 8:
{
lean_object* v_alt_302_; lean_object* v_url_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec_ref(v_x_56_);
v_alt_302_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_alt_302_);
v_url_303_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_url_303_);
lean_dec_ref_known(v_x_57_, 2);
v___x_304_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__17));
v___x_305_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_302_);
lean_dec_ref(v_alt_302_);
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__11));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
v___x_309_ = lean_string_append(v___x_308_, v_url_303_);
lean_dec_ref(v_url_303_);
v___x_310_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__12));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_array_push(v___x_313_, v___x_311_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
case 9:
{
lean_object* v_content_316_; size_t v_sz_317_; size_t v___x_318_; lean_object* v___x_319_; 
v_content_316_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_content_316_);
lean_dec_ref_known(v_x_57_, 1);
v_sz_317_ = lean_array_size(v_content_316_);
v___x_318_ = ((size_t)0ULL);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_56_, v_sz_317_, v___x_318_, v_content_316_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = l_Lean_Doc_joinInlines(v_a_320_);
lean_dec(v_a_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_a_329_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_319_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_319_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
default: 
{
lean_object* v_container_337_; 
v_container_337_ = lean_ctor_get(v_x_57_, 0);
if (lean_obj_tag(v_container_337_) == 0)
{
lean_object* v_content_338_; lean_object* v_val_339_; lean_object* v___x_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_fallback_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc_ref(v_container_337_);
v_content_338_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref_n(v_content_338_, 2);
lean_dec_ref_known(v_x_57_, 2);
v_val_339_ = lean_ctor_get(v_container_337_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_container_337_, 1);
lean_inc_ref_n(v_x_56_, 2);
v___x_340_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed), 6, 1);
lean_closure_set(v___x_340_, 0, v_x_56_);
v_sz_341_ = lean_array_size(v_content_338_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_box_usize(v_sz_341_);
v___x_344_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1));
v_fallback_345_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0___boxed), 8, 4);
lean_closure_set(v_fallback_345_, 0, v_x_56_);
lean_closure_set(v_fallback_345_, 1, v___x_343_);
lean_closure_set(v_fallback_345_, 2, v___x_344_);
lean_closure_set(v_fallback_345_, 3, v_content_338_);
v___x_346_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_339_);
v___x_347_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_346_, v_a_59_, v_a_60_);
lean_dec(v___x_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
if (lean_obj_tag(v_a_348_) == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v_fallback_345_);
lean_dec_ref(v___x_340_);
lean_dec(v_val_339_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_56_, v_sz_341_, v___x_342_, v_content_338_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_Doc_joinInlines(v_a_350_);
lean_dec(v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_349_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_349_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_val_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec_ref(v_x_56_);
v_val_367_ = lean_ctor_get(v_a_348_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_a_348_, 1);
v___x_368_ = lean_apply_3(v_val_367_, v___x_340_, v_val_339_, v_content_338_);
v___x_369_ = l_Lean_Doc_withRendererFallback(v_fallback_345_, v___x_368_, v_a_58_, v_a_59_, v_a_60_);
return v___x_369_;
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_fallback_345_);
lean_dec_ref(v___x_340_);
lean_dec(v_val_339_);
lean_dec_ref(v_content_338_);
lean_dec_ref(v_x_56_);
v_a_370_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_347_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_347_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_content_378_; size_t v_sz_379_; size_t v___x_380_; lean_object* v___x_381_; 
v_content_378_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_content_378_);
lean_dec_ref_known(v_x_57_, 2);
v_sz_379_ = lean_array_size(v_content_378_);
v___x_380_ = ((size_t)0ULL);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_56_, v_sz_379_, v___x_380_, v_content_378_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = l_Lean_Doc_joinInlines(v_a_382_);
lean_dec(v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_381_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = l_Lean_Doc_joinInlines(v_pieces_63_);
lean_dec_ref(v_pieces_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = l_Lean_Doc_joinInlines(v_pieces_67_);
lean_dec_ref(v_pieces_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(lean_object* v_x_399_, size_t v_sz_400_, size_t v_i_401_, lean_object* v_bs_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_x_399_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_bs_402_);
return v___x_408_;
}
else
{
lean_object* v_v_409_; lean_object* v___x_410_; lean_object* v_bs_x27_411_; lean_object* v___x_412_; 
v_v_409_ = lean_array_uget(v_bs_402_, v_i_401_);
v___x_410_ = lean_unsigned_to_nat(0u);
v_bs_x27_411_ = lean_array_uset(v_bs_402_, v_i_401_, v___x_410_);
lean_inc_ref(v_x_399_);
v___x_412_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v_x_399_, v_v_409_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_401_, v___x_414_);
v___x_416_ = lean_array_uset(v_bs_x27_411_, v_i_401_, v_a_413_);
v_i_401_ = v___x_415_;
v_bs_402_ = v___x_416_;
goto _start;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_bs_x27_411_);
lean_dec_ref(v_x_399_);
v_a_418_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_412_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_412_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(lean_object* v_x_426_, size_t v_sz_427_, size_t v___x_428_, lean_object* v_content_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_426_, v_sz_427_, v___x_428_, v_content_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = l_Lean_Doc_joinInlines(v_a_435_);
lean_dec(v_a_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_434_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_434_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4___boxed(lean_object* v_x_452_, lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
size_t v_sz_boxed_460_; size_t v_i_boxed_461_; lean_object* v_res_462_; 
v_sz_boxed_460_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_461_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_452_, v_sz_boxed_460_, v_i_boxed_461_, v_bs_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__9(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_zero_465_; uint8_t v_isZero_466_; 
v_zero_465_ = lean_unsigned_to_nat(0u);
v_isZero_466_ = lean_nat_dec_eq(v_x_463_, v_zero_465_);
if (v_isZero_466_ == 1)
{
lean_dec(v_x_463_);
return v_x_464_;
}
else
{
uint32_t v___x_467_; lean_object* v_one_468_; lean_object* v_n_469_; lean_object* v___x_470_; 
v___x_467_ = 32;
v_one_468_ = lean_unsigned_to_nat(1u);
v_n_469_ = lean_nat_sub(v_x_463_, v_one_468_);
lean_dec(v_x_463_);
v___x_470_ = lean_string_push(v_x_464_, v___x_467_);
v_x_463_ = v_n_469_;
v_x_464_ = v___x_470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(size_t v_sz_476_, size_t v_i_477_, lean_object* v_bs_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_477_, v_sz_476_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_bs_478_);
return v___x_484_;
}
else
{
lean_object* v_v_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; 
v_v_485_ = lean_array_uget(v_bs_478_, v_i_477_);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_478_, v_i_477_, v___x_486_);
v_sz_488_ = lean_array_size(v_v_485_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_488_, v___x_489_, v_v_485_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0));
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1));
v___x_494_ = l_Lean_Doc_joinBlocks(v_a_491_);
lean_dec(v_a_491_);
v___x_495_ = l_Lean_Doc_prefixListLines(v___x_492_, v___x_493_, v___x_494_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_477_, v___x_496_);
v___x_498_ = lean_array_uset(v_bs_x27_487_, v_i_477_, v___x_495_);
v_i_477_ = v___x_497_;
v_bs_478_ = v___x_498_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_487_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_b_504_);
return v___x_510_;
}
else
{
lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_546_; 
v_fst_511_ = lean_ctor_get(v_b_504_, 0);
v_snd_512_ = lean_ctor_get(v_b_504_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_b_504_);
if (v_isSharedCheck_546_ == 0)
{
v___x_514_ = v_b_504_;
v_isShared_515_ = v_isSharedCheck_546_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_511_);
lean_dec(v_b_504_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_546_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; size_t v_sz_524_; size_t v___x_525_; lean_object* v___x_526_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v_a_517_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
lean_inc(v_snd_512_);
v___x_518_ = l_Nat_reprFast(v_snd_512_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___closed__0));
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_522_ = lean_string_utf8_byte_size(v___x_520_);
v___x_523_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__9(v___x_522_, v___x_521_);
v_sz_524_ = lean_array_size(v_a_517_);
v___x_525_ = ((size_t)0ULL);
lean_inc(v_a_517_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_524_, v___x_525_, v_a_517_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_Doc_joinBlocks(v_a_527_);
lean_dec(v_a_527_);
v___x_529_ = l_Lean_Doc_prefixListLines(v___x_520_, v___x_523_, v___x_528_);
v___x_530_ = lean_array_push(v_fst_511_, v___x_529_);
v___x_531_ = lean_nat_add(v_snd_512_, v___x_516_);
lean_dec(v_snd_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_531_);
lean_ctor_set(v___x_514_, 0, v___x_530_);
v___x_533_ = v___x_514_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
size_t v___x_534_; size_t v___x_535_; 
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_add(v_i_503_, v___x_534_);
v_i_503_ = v___x_535_;
v_b_504_ = v___x_533_;
goto _start;
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___x_523_);
lean_dec_ref(v___x_520_);
lean_del_object(v___x_514_);
lean_dec(v_snd_512_);
lean_dec(v_fst_511_);
v_a_538_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_526_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(size_t v_sz_552_, size_t v_i_553_, lean_object* v_bs_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_553_, v_sz_552_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_bs_554_);
return v___x_560_;
}
else
{
lean_object* v_v_561_; lean_object* v___x_562_; lean_object* v_term_563_; lean_object* v_desc_564_; lean_object* v___x_565_; lean_object* v_bs_x27_566_; lean_object* v_a_568_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_v_561_ = lean_array_uget_borrowed(v_bs_554_, v_i_553_);
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
v_term_563_ = lean_ctor_get(v_v_561_, 0);
lean_inc_ref(v_term_563_);
v_desc_564_ = lean_ctor_get(v_v_561_, 1);
lean_inc_ref(v_desc_564_);
v___x_565_ = lean_unsigned_to_nat(0u);
v_bs_x27_566_ = lean_array_uset(v_bs_554_, v_i_553_, v___x_565_);
v___x_573_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_573_, 0, v_term_563_);
v___x_574_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_562_, v___x_573_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; size_t v_sz_576_; size_t v___x_577_; lean_object* v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v_sz_576_ = lean_array_size(v_desc_564_);
v___x_577_ = ((size_t)0ULL);
lean_inc_ref(v_desc_564_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_576_, v___x_577_, v_desc_564_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___y_581_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_mk_empty_array_with_capacity(v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__2));
v___x_588_ = lean_unsigned_to_nat(2u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_array_push(v___x_589_, v_a_575_);
v___x_591_ = lean_array_push(v___x_590_, v___x_587_);
v___x_592_ = l_Lean_Doc_joinInlines(v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = lean_array_get_size(v_desc_564_);
lean_dec_ref(v_desc_564_);
v___x_594_ = lean_nat_dec_le(v___x_593_, v___x_585_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_array_push(v___x_586_, v___x_592_);
v___x_596_ = l_Array_append___redArg(v___x_595_, v_a_579_);
lean_dec(v_a_579_);
v___x_597_ = l_Lean_Doc_joinBlocks(v___x_596_);
lean_dec_ref(v___x_596_);
v___y_581_ = v___x_597_;
goto v___jp_580_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec_ref(v___x_586_);
v___x_598_ = l_Lean_Doc_joinBlocks(v_a_579_);
lean_dec(v_a_579_);
v___x_599_ = l_Array_append___redArg(v___x_592_, v___x_598_);
lean_dec_ref(v___x_598_);
v___y_581_ = v___x_599_;
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0));
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1));
v___x_584_ = l_Lean_Doc_prefixListLines(v___x_582_, v___x_583_, v___y_581_);
v_a_568_ = v___x_584_;
goto v___jp_567_;
}
}
else
{
lean_dec(v_a_575_);
lean_dec_ref(v_bs_x27_566_);
lean_dec_ref(v_desc_564_);
return v___x_578_;
}
}
else
{
lean_dec_ref(v_desc_564_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_600_; 
v_a_600_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_574_, 1);
v_a_568_ = v_a_600_;
goto v___jp_567_;
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_bs_x27_566_);
v_a_601_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_574_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_574_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
v___jp_567_:
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_553_, v___x_569_);
v___x_571_ = lean_array_uset(v_bs_x27_566_, v_i_553_, v_a_568_);
v_i_553_ = v___x_570_;
v_bs_554_ = v___x_571_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed(lean_object* v_x_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_x_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed(lean_object* v_sz_618_, lean_object* v___x_619_, lean_object* v_content_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
size_t v_sz_boxed_625_; size_t v___x_6914__boxed_626_; lean_object* v_res_627_; 
v_sz_boxed_625_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v___x_6914__boxed_626_ = lean_unbox_usize(v___x_619_);
lean_dec(v___x_619_);
v_res_627_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(v_sz_boxed_625_, v___x_6914__boxed_626_, v_content_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
switch(lean_obj_tag(v_x_628_))
{
case 0:
{
lean_object* v_contents_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_642_; 
v_contents_633_ = lean_ctor_get(v_x_628_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_642_ == 0)
{
v___x_635_ = v_x_628_;
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_contents_633_);
lean_dec(v_x_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 9);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_contents_633_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_637_, v___x_639_, v_a_629_, v_a_630_, v_a_631_);
return v___x_640_;
}
}
}
case 1:
{
lean_object* v_content_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_content_643_ = lean_ctor_get(v_x_628_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_x_628_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_content_643_);
lean_dec(v_x_628_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
case 2:
{
lean_object* v_items_652_; size_t v_sz_653_; size_t v___x_654_; lean_object* v___x_655_; 
v_items_652_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_items_652_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_653_ = lean_array_size(v_items_652_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_653_, v___x_654_, v_items_652_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_Doc_joinBlocks(v_a_656_);
lean_dec(v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
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
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_655_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
case 3:
{
lean_object* v_start_673_; lean_object* v_items_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_708_; 
v_start_673_ = lean_ctor_get(v_x_628_, 0);
v_items_674_ = lean_ctor_get(v_x_628_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_708_ == 0)
{
v___x_676_ = v_x_628_;
v_isShared_677_ = v_isSharedCheck_708_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_items_674_);
lean_inc(v_start_673_);
lean_dec(v_x_628_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_708_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_out_678_; lean_object* v___y_680_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_out_678_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2));
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = l_Int_toNat(v_start_673_);
lean_dec(v_start_673_);
v___x_707_ = lean_nat_dec_le(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v___x_706_);
v___y_680_ = v___x_705_;
goto v___jp_679_;
}
else
{
v___y_680_ = v___x_706_;
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
lean_ctor_set(v___x_676_, 1, v___y_680_);
lean_ctor_set(v___x_676_, 0, v_out_678_);
v___x_682_ = v___x_676_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_out_678_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___y_680_);
v___x_682_ = v_reuseFailAlloc_704_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
size_t v_sz_683_; size_t v___x_684_; lean_object* v___x_685_; 
v_sz_683_ = lean_array_size(v_items_674_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_items_674_, v_sz_683_, v___x_684_, v___x_682_, v_a_629_, v_a_630_, v_a_631_);
lean_dec_ref(v_items_674_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_fst_690_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_fst_690_);
lean_dec(v_a_686_);
v___x_691_ = l_Lean_Doc_joinBlocks(v_fst_690_);
lean_dec(v_fst_690_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_685_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_685_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_709_; size_t v_sz_710_; size_t v___x_711_; lean_object* v___x_712_; 
v_items_709_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_items_709_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_710_ = lean_array_size(v_items_709_);
v___x_711_ = ((size_t)0ULL);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_710_, v___x_711_, v_items_709_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_721_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_Doc_joinBlocks(v_a_713_);
lean_dec(v_a_713_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_712_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_712_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
case 5:
{
lean_object* v_items_730_; size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; 
v_items_730_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_items_730_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_731_ = lean_array_size(v_items_730_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_731_, v___x_732_, v_items_730_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_744_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_744_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_738_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__0));
v___x_739_ = l_Lean_Doc_joinBlocks(v_a_734_);
lean_dec(v_a_734_);
v___x_740_ = l_Lean_Doc_prefixLines(v___x_738_, v___x_739_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_733_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_733_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
case 6:
{
lean_object* v_content_753_; size_t v_sz_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_content_753_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_content_753_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_754_ = lean_array_size(v_content_753_);
v___x_755_ = ((size_t)0ULL);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_754_, v___x_755_, v_content_753_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = l_Lean_Doc_joinBlocks(v_a_757_);
lean_dec(v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_756_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
default: 
{
lean_object* v_container_774_; 
v_container_774_ = lean_ctor_get(v_x_628_, 0);
if (lean_obj_tag(v_container_774_) == 0)
{
lean_object* v_content_775_; lean_object* v_val_776_; lean_object* v___x_777_; lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v_fallback_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc_ref(v_container_774_);
v_content_775_ = lean_ctor_get(v_x_628_, 1);
lean_inc_ref_n(v_content_775_, 2);
lean_dec_ref_known(v_x_628_, 2);
v_val_776_ = lean_ctor_get(v_container_774_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_container_774_, 1);
v___x_777_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__1));
v___x_778_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed), 5, 0);
v_sz_779_ = lean_array_size(v_content_775_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_box_usize(v_sz_779_);
v___x_782_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1));
v_fallback_783_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed), 7, 3);
lean_closure_set(v_fallback_783_, 0, v___x_781_);
lean_closure_set(v_fallback_783_, 1, v___x_782_);
lean_closure_set(v_fallback_783_, 2, v_content_775_);
v___x_784_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_776_);
v___x_785_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_784_, v_a_630_, v_a_631_);
lean_dec(v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
if (lean_obj_tag(v_a_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v_fallback_783_);
lean_dec_ref(v___x_778_);
lean_dec(v_val_776_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_779_, v___x_780_, v_content_775_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_Doc_joinBlocks(v_a_788_);
lean_dec(v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_787_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_787_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_val_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_val_805_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_786_, 1);
v___x_806_ = lean_apply_4(v_val_805_, v___x_777_, v___x_778_, v_val_776_, v_content_775_);
v___x_807_ = l_Lean_Doc_withRendererFallback(v_fallback_783_, v___x_806_, v_a_629_, v_a_630_, v_a_631_);
return v___x_807_;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_fallback_783_);
lean_dec_ref(v___x_778_);
lean_dec(v_val_776_);
lean_dec_ref(v_content_775_);
v_a_808_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_785_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_785_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_content_816_; size_t v_sz_817_; size_t v___x_818_; lean_object* v___x_819_; 
v_content_816_ = lean_ctor_get(v_x_628_, 1);
lean_inc_ref(v_content_816_);
lean_dec_ref_known(v_x_628_, 2);
v_sz_817_ = lean_array_size(v_content_816_);
v___x_818_ = ((size_t)0ULL);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_817_, v___x_818_, v_content_816_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_828_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = l_Lean_Doc_joinBlocks(v_a_820_);
lean_dec(v_a_820_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_819_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(size_t v_sz_837_, size_t v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_bs_839_);
return v___x_845_;
}
else
{
lean_object* v_v_846_; lean_object* v___x_847_; lean_object* v_bs_x27_848_; lean_object* v___x_849_; 
v_v_846_ = lean_array_uget(v_bs_839_, v_i_838_);
v___x_847_ = lean_unsigned_to_nat(0u);
v_bs_x27_848_ = lean_array_uset(v_bs_839_, v_i_838_, v___x_847_);
v___x_849_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_v_846_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_838_, v___x_851_);
v___x_853_ = lean_array_uset(v_bs_x27_848_, v_i_838_, v_a_850_);
v_i_838_ = v___x_852_;
v_bs_839_ = v___x_853_;
goto _start;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_bs_x27_848_);
v_a_855_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_849_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_849_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(size_t v_sz_863_, size_t v___x_864_, lean_object* v_content_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_863_, v___x_864_, v_content_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = l_Lean_Doc_joinBlocks(v_a_871_);
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_870_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_870_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7___boxed(lean_object* v_sz_888_, lean_object* v_i_889_, lean_object* v_bs_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v_i_boxed_896_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_boxed_895_, v_i_boxed_896_, v_bs_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___boxed(lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_bs_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
size_t v_sz_boxed_905_; size_t v_i_boxed_906_; lean_object* v_res_907_; 
v_sz_boxed_905_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_906_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_boxed_905_, v_i_boxed_906_, v_bs_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___boxed(lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_917_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_as_908_, v_sz_boxed_916_, v_i_boxed_917_, v_b_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v_as_908_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___boxed(lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_bs_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_927_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_boxed_926_, v_i_boxed_927_, v_bs_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(size_t v_sz_929_, size_t v_i_930_, lean_object* v_bs_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_930_, v_sz_929_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_bs_931_);
return v___x_937_;
}
else
{
lean_object* v_v_938_; lean_object* v___x_939_; lean_object* v_bs_x27_940_; lean_object* v___x_941_; 
v_v_938_ = lean_array_uget(v_bs_931_, v_i_930_);
v___x_939_ = lean_unsigned_to_nat(0u);
v_bs_x27_940_ = lean_array_uset(v_bs_931_, v_i_930_, v___x_939_);
v___x_941_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_v_938_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_930_, v___x_943_);
v___x_945_ = lean_array_uset(v_bs_x27_940_, v_i_930_, v_a_942_);
v_i_930_ = v___x_944_;
v_bs_931_ = v___x_945_;
goto _start;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_bs_x27_940_);
v_a_947_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_941_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_941_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed(lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_bs_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_963_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_boxed_962_, v_i_boxed_963_, v_bs_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v_zero_967_; uint8_t v_isZero_968_; 
v_zero_967_ = lean_unsigned_to_nat(0u);
v_isZero_968_ = lean_nat_dec_eq(v_x_965_, v_zero_967_);
if (v_isZero_968_ == 1)
{
lean_dec(v_x_965_);
return v_x_966_;
}
else
{
uint32_t v___x_969_; lean_object* v_one_970_; lean_object* v_n_971_; lean_object* v___x_972_; 
v___x_969_ = 35;
v_one_970_ = lean_unsigned_to_nat(1u);
v_n_971_ = lean_nat_sub(v_x_965_, v_one_970_);
lean_dec(v_x_965_);
v___x_972_ = lean_string_push(v_x_966_, v___x_969_);
v_x_965_ = v_n_971_;
v_x_966_ = v___x_972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(size_t v_sz_974_, size_t v_i_975_, lean_object* v_bs_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_lt(v_i_975_, v_sz_974_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_bs_976_);
return v___x_982_;
}
else
{
lean_object* v_v_983_; lean_object* v___x_984_; lean_object* v_bs_x27_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_v_983_ = lean_array_uget(v_bs_976_, v_i_975_);
v___x_984_ = lean_unsigned_to_nat(0u);
v_bs_x27_985_ = lean_array_uset(v_bs_976_, v_i_975_, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
v___x_987_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_986_, v_v_983_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_975_, v___x_989_);
v___x_991_ = lean_array_uset(v_bs_x27_985_, v_i_975_, v_a_988_);
v_i_975_ = v___x_990_;
v_bs_976_ = v___x_991_;
goto _start;
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_bs_x27_985_);
v_a_993_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_987_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_987_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___boxed(lean_object* v_sz_1001_, lean_object* v_i_1002_, lean_object* v_bs_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
size_t v_sz_boxed_1008_; size_t v_i_boxed_1009_; lean_object* v_res_1010_; 
v_sz_boxed_1008_ = lean_unbox_usize(v_sz_1001_);
lean_dec(v_sz_1001_);
v_i_boxed_1009_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_boxed_1008_, v_i_boxed_1009_, v_bs_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(lean_object* v_level_1012_, lean_object* v_part_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_title_1018_; lean_object* v_content_1019_; lean_object* v_subParts_1020_; size_t v_sz_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v_title_1018_ = lean_ctor_get(v_part_1013_, 0);
lean_inc_ref(v_title_1018_);
v_content_1019_ = lean_ctor_get(v_part_1013_, 3);
lean_inc_ref(v_content_1019_);
v_subParts_1020_ = lean_ctor_get(v_part_1013_, 4);
lean_inc_ref(v_subParts_1020_);
lean_dec_ref(v_part_1013_);
v_sz_1021_ = lean_array_size(v_title_1018_);
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_1021_, v___x_1022_, v_title_1018_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; size_t v_sz_1036_; lean_object* v___x_1037_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_level_1012_, v___x_1026_);
lean_inc(v___x_1027_);
v___x_1028_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(v___x_1027_, v___x_1025_);
v___x_1029_ = ((lean_object*)(l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___closed__0));
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
v___x_1031_ = lean_mk_empty_array_with_capacity(v___x_1026_);
lean_inc_ref_n(v___x_1031_, 2);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1030_);
v___x_1033_ = lean_array_push(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Array_append___redArg(v___x_1033_, v_a_1024_);
lean_dec(v_a_1024_);
v___x_1035_ = l_Lean_Doc_joinInlines(v___x_1034_);
lean_dec_ref(v___x_1034_);
v_sz_1036_ = lean_array_size(v_content_1019_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_1036_, v___x_1022_, v_content_1019_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; size_t v_sz_1039_; lean_object* v___x_1040_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v_sz_1039_ = lean_array_size(v_subParts_1020_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1027_, v_sz_1039_, v___x_1022_, v_subParts_1020_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v___x_1027_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1052_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1045_ = lean_array_push(v___x_1031_, v___x_1035_);
v___x_1046_ = l_Array_append___redArg(v___x_1045_, v_a_1038_);
lean_dec(v_a_1038_);
v___x_1047_ = l_Array_append___redArg(v___x_1046_, v_a_1041_);
lean_dec(v_a_1041_);
v___x_1048_ = l_Lean_Doc_joinBlocks(v___x_1047_);
lean_dec_ref(v___x_1047_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1048_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1038_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1031_);
v_a_1053_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1040_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1040_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1031_);
lean_dec(v___x_1027_);
lean_dec_ref(v_subParts_1020_);
v_a_1061_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1037_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1037_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v_subParts_1020_);
lean_dec_ref(v_content_1019_);
v_a_1069_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1023_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1023_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(lean_object* v___x_1077_, size_t v_sz_1078_, size_t v_i_1079_, lean_object* v_bs_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_lt(v_i_1079_, v_sz_1078_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_bs_1080_);
return v___x_1086_;
}
else
{
lean_object* v_v_1087_; lean_object* v___x_1088_; lean_object* v_bs_x27_1089_; lean_object* v___x_1090_; 
v_v_1087_ = lean_array_uget(v_bs_1080_, v_i_1079_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v_bs_x27_1089_ = lean_array_uset(v_bs_1080_, v_i_1079_, v___x_1088_);
v___x_1090_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v___x_1077_, v_v_1087_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_add(v_i_1079_, v___x_1092_);
v___x_1094_ = lean_array_uset(v_bs_x27_1089_, v_i_1079_, v_a_1091_);
v_i_1079_ = v___x_1093_;
v_bs_1080_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_bs_x27_1089_);
v_a_1096_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1090_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1090_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg___boxed(lean_object* v___x_1104_, lean_object* v_sz_1105_, lean_object* v_i_1106_, lean_object* v_bs_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
size_t v_sz_boxed_1112_; size_t v_i_boxed_1113_; lean_object* v_res_1114_; 
v_sz_boxed_1112_ = lean_unbox_usize(v_sz_1105_);
lean_dec(v_sz_1105_);
v_i_boxed_1113_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1104_, v_sz_boxed_1112_, v_i_boxed_1113_, v_bs_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___x_1104_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___boxed(lean_object* v_level_1115_, lean_object* v_part_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1115_, v_part_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec(v_level_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(size_t v_sz_1122_, size_t v_i_1123_, lean_object* v_bs_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_usize_dec_lt(v_i_1123_, v_sz_1122_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_bs_1124_);
return v___x_1130_;
}
else
{
lean_object* v_v_1131_; lean_object* v___x_1132_; lean_object* v_bs_x27_1133_; lean_object* v___x_1134_; 
v_v_1131_ = lean_array_uget(v_bs_1124_, v_i_1123_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v_bs_x27_1133_ = lean_array_uset(v_bs_1124_, v_i_1123_, v___x_1132_);
v___x_1134_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v___x_1132_, v_v_1131_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_i_1123_, v___x_1136_);
v___x_1138_ = lean_array_uset(v_bs_x27_1133_, v_i_1123_, v_a_1135_);
v_i_1123_ = v___x_1137_;
v_bs_1124_ = v___x_1138_;
goto _start;
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_bs_x27_1133_);
v_a_1140_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1134_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1134_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4___boxed(lean_object* v_sz_1148_, lean_object* v_i_1149_, lean_object* v_bs_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1148_);
lean_dec(v_sz_1148_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(lean_object* v_fst_1158_, lean_object* v_snd_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v_sz_1164_ = lean_array_size(v_fst_1158_);
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_1164_, v___x_1165_, v_fst_1158_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; size_t v_sz_1168_; lean_object* v___x_1169_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v_sz_1168_ = lean_array_size(v_snd_1159_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_1168_, v___x_1165_, v_snd_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1179_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = l_Array_append___redArg(v_a_1167_, v_a_1170_);
lean_dec(v_a_1170_);
v___x_1175_ = l_Lean_Doc_joinBlocks(v___x_1174_);
lean_dec_ref(v___x_1174_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1167_);
v_a_1180_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1169_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1169_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_snd_1159_);
v_a_1188_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1166_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1166_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed(lean_object* v_fst_1196_, lean_object* v_snd_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(v_fst_1196_, v_snd_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
lean_ctor_set(v___x_1208_, 3, v___x_1207_);
lean_ctor_set(v___x_1208_, 4, v___x_1206_);
lean_ctor_set(v___x_1208_, 5, v___x_1206_);
lean_ctor_set(v___x_1208_, 6, v___x_1206_);
lean_ctor_set(v___x_1208_, 7, v___x_1206_);
lean_ctor_set(v___x_1208_, 8, v___x_1206_);
lean_ctor_set(v___x_1208_, 9, v___x_1206_);
lean_ctor_set(v___x_1208_, 10, v___x_1206_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(32u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_unsigned_to_nat(32u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3);
v___x_1217_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1215_);
lean_ctor_set(v___x_1217_, 2, v___x_1213_);
lean_ctor_set(v___x_1217_, 3, v___x_1213_);
lean_ctor_set_usize(v___x_1217_, 4, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_box(1);
v___x_1219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_1220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
lean_ctor_set(v___x_1221_, 2, v___x_1218_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_msgData_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v_env_1226_; uint8_t v___x_1227_; lean_object* v_env_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_scopes_1231_; lean_object* v___x_1232_; lean_object* v_opts_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1225_ = lean_st_ref_get(v___y_1223_);
v_env_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_ref(v_env_1226_);
lean_dec(v___x_1225_);
v___x_1227_ = 0;
v_env_1228_ = l_Lean_Environment_setRecordingDeps(v_env_1226_, v___x_1227_);
v___x_1229_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1230_ = lean_st_ref_get(v___y_1223_);
v_scopes_1231_ = lean_ctor_get(v___x_1230_, 2);
lean_inc(v_scopes_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = l_List_head_x21___redArg(v___x_1229_, v_scopes_1231_);
lean_dec(v_scopes_1231_);
v_opts_1233_ = lean_ctor_get(v___x_1232_, 1);
lean_inc_ref(v_opts_1233_);
lean_dec(v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2);
v___x_1235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5);
v___x_1236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1236_, 0, v_env_1228_);
lean_ctor_set(v___x_1236_, 1, v___x_1234_);
lean_ctor_set(v___x_1236_, 2, v___x_1235_);
lean_ctor_set(v___x_1236_, 3, v_opts_1233_);
v___x_1237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_msgData_1222_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_msgData_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1239_, v___y_1240_);
lean_dec(v___y_1240_);
return v_res_1242_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(1);
v___x_1244_ = l_Lean_MessageData_ofFormat(v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2));
v___x_1249_ = l_Lean_MessageData_ofFormat(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
return v_x_1250_;
}
else
{
lean_object* v_head_1252_; lean_object* v_tail_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1275_; 
v_head_1252_ = lean_ctor_get(v_x_1251_, 0);
v_tail_1253_ = lean_ctor_get(v_x_1251_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1255_ = v_x_1251_;
v_isShared_1256_ = v_isSharedCheck_1275_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_tail_1253_);
lean_inc(v_head_1252_);
lean_dec(v_x_1251_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1275_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_before_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1273_; 
v_before_1257_ = lean_ctor_get(v_head_1252_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_head_1252_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_head_1252_, 1);
lean_dec(v_unused_1274_);
v___x_1259_ = v_head_1252_;
v_isShared_1260_ = v_isSharedCheck_1273_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_before_1257_);
lean_dec(v_head_1252_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1273_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 7);
lean_ctor_set(v___x_1259_, 1, v___x_1261_);
lean_ctor_set(v___x_1259_, 0, v_x_1250_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_x_1250_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 7);
lean_ctor_set(v___x_1255_, 1, v___x_1264_);
lean_ctor_set(v___x_1255_, 0, v___x_1263_);
v___x_1266_ = v___x_1255_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = l_Lean_MessageData_ofSyntax(v_before_1257_);
v___x_1268_ = l_Lean_indentD(v___x_1267_);
v___x_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1266_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v_x_1250_ = v___x_1269_;
v_x_1251_ = v_tail_1253_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(lean_object* v_opts_1276_, lean_object* v_opt_1277_){
_start:
{
lean_object* v_name_1278_; lean_object* v_defValue_1279_; lean_object* v_map_1280_; lean_object* v___x_1281_; 
v_name_1278_ = lean_ctor_get(v_opt_1277_, 0);
v_defValue_1279_ = lean_ctor_get(v_opt_1277_, 1);
v_map_1280_ = lean_ctor_get(v_opts_1276_, 0);
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1280_, v_name_1278_);
if (lean_obj_tag(v___x_1281_) == 0)
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_unbox(v_defValue_1279_);
return v___x_1282_;
}
else
{
lean_object* v_val_1283_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1281_, 1);
if (lean_obj_tag(v_val_1283_) == 1)
{
uint8_t v_v_1284_; 
v_v_1284_ = lean_ctor_get_uint8(v_val_1283_, 0);
lean_dec_ref_known(v_val_1283_, 0);
return v_v_1284_;
}
else
{
uint8_t v___x_1285_; 
lean_dec(v_val_1283_);
v___x_1285_ = lean_unbox(v_defValue_1279_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17___boxed(lean_object* v_opts_1286_, lean_object* v_opt_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1286_, v_opt_1287_);
lean_dec_ref(v_opt_1287_);
lean_dec_ref(v_opts_1286_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1));
v___x_1294_ = l_Lean_MessageData_ofFormat(v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_msgData_1295_, lean_object* v_macroStack_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_scopes_1301_; lean_object* v___x_1302_; lean_object* v_opts_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1299_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1300_ = lean_st_ref_get(v___y_1297_);
v_scopes_1301_ = lean_ctor_get(v___x_1300_, 2);
lean_inc(v_scopes_1301_);
lean_dec(v___x_1300_);
v___x_1302_ = l_List_head_x21___redArg(v___x_1299_, v_scopes_1301_);
lean_dec(v_scopes_1301_);
v_opts_1303_ = lean_ctor_get(v___x_1302_, 1);
lean_inc_ref(v_opts_1303_);
lean_dec(v___x_1302_);
v___x_1304_ = l_Lean_Elab_pp_macroStack;
v___x_1305_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1303_, v___x_1304_);
lean_dec_ref(v_opts_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v_macroStack_1296_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_msgData_1295_);
return v___x_1306_;
}
else
{
if (lean_obj_tag(v_macroStack_1296_) == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_msgData_1295_);
return v___x_1307_;
}
else
{
lean_object* v_head_1308_; lean_object* v_after_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1324_; 
v_head_1308_ = lean_ctor_get(v_macroStack_1296_, 0);
lean_inc(v_head_1308_);
v_after_1309_ = lean_ctor_get(v_head_1308_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_head_1308_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_head_1308_, 0);
lean_dec(v_unused_1325_);
v___x_1311_ = v_head_1308_;
v_isShared_1312_ = v_isSharedCheck_1324_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_after_1309_);
lean_dec(v_head_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1324_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 7);
lean_ctor_set(v___x_1311_, 1, v___x_1313_);
lean_ctor_set(v___x_1311_, 0, v_msgData_1295_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_msgData_1295_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_msgData_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1316_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_MessageData_ofSyntax(v_after_1309_);
v___x_1319_ = l_Lean_indentD(v___x_1318_);
v_msgData_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1320_, 0, v___x_1317_);
lean_ctor_set(v_msgData_1320_, 1, v___x_1319_);
v___x_1321_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(v_msgData_1320_, v_macroStack_1296_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_msgData_1326_, lean_object* v_macroStack_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1326_, v_macroStack_1327_, v___y_1328_);
lean_dec(v___y_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Elab_Command_getRef___redArg(v___y_1332_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_macroStack_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v_macroStack_1337_ = lean_ctor_get(v___y_1332_, 4);
v___x_1338_ = l_Lean_Elab_getBetterRef(v_a_1336_, v_macroStack_1337_);
lean_dec(v_a_1336_);
v___x_1339_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msg_1331_, v___y_1333_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
lean_inc(v_macroStack_1337_);
v___x_1341_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_a_1340_, v_macroStack_1337_, v___y_1333_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1338_);
lean_ctor_set(v___x_1346_, 1, v_a_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 1);
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_msg_1331_);
v_a_1351_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1335_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1335_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object* v_ref_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Elab_Command_getRef___redArg(v___y_1366_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_fileName_1371_; lean_object* v_fileMap_1372_; lean_object* v_currRecDepth_1373_; lean_object* v_cmdPos_1374_; lean_object* v_macroStack_1375_; lean_object* v_quotContext_x3f_1376_; lean_object* v_currMacroScope_1377_; lean_object* v_snap_x3f_1378_; lean_object* v_cancelTk_x3f_1379_; uint8_t v_suppressElabErrors_1380_; lean_object* v_ref_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_fileName_1371_ = lean_ctor_get(v___y_1366_, 0);
v_fileMap_1372_ = lean_ctor_get(v___y_1366_, 1);
v_currRecDepth_1373_ = lean_ctor_get(v___y_1366_, 2);
v_cmdPos_1374_ = lean_ctor_get(v___y_1366_, 3);
v_macroStack_1375_ = lean_ctor_get(v___y_1366_, 4);
v_quotContext_x3f_1376_ = lean_ctor_get(v___y_1366_, 5);
v_currMacroScope_1377_ = lean_ctor_get(v___y_1366_, 6);
v_snap_x3f_1378_ = lean_ctor_get(v___y_1366_, 8);
v_cancelTk_x3f_1379_ = lean_ctor_get(v___y_1366_, 9);
v_suppressElabErrors_1380_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*10);
v_ref_1381_ = l_Lean_replaceRef(v_ref_1364_, v_a_1370_);
lean_dec(v_a_1370_);
lean_inc(v_cancelTk_x3f_1379_);
lean_inc(v_snap_x3f_1378_);
lean_inc(v_currMacroScope_1377_);
lean_inc(v_quotContext_x3f_1376_);
lean_inc(v_macroStack_1375_);
lean_inc(v_cmdPos_1374_);
lean_inc(v_currRecDepth_1373_);
lean_inc_ref(v_fileMap_1372_);
lean_inc_ref(v_fileName_1371_);
v___x_1382_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1382_, 0, v_fileName_1371_);
lean_ctor_set(v___x_1382_, 1, v_fileMap_1372_);
lean_ctor_set(v___x_1382_, 2, v_currRecDepth_1373_);
lean_ctor_set(v___x_1382_, 3, v_cmdPos_1374_);
lean_ctor_set(v___x_1382_, 4, v_macroStack_1375_);
lean_ctor_set(v___x_1382_, 5, v_quotContext_x3f_1376_);
lean_ctor_set(v___x_1382_, 6, v_currMacroScope_1377_);
lean_ctor_set(v___x_1382_, 7, v_ref_1381_);
lean_ctor_set(v___x_1382_, 8, v_snap_x3f_1378_);
lean_ctor_set(v___x_1382_, 9, v_cancelTk_x3f_1379_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*10, v_suppressElabErrors_1380_);
v___x_1383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1365_, v___x_1382_, v___y_1367_);
lean_dec_ref_known(v___x_1382_, 10);
return v___x_1383_;
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_msg_1365_);
v_a_1384_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1369_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1369_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object* v_ref_1392_, lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1392_, v_msg_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v_ref_1392_);
return v_res_1397_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0));
v___x_1400_ = l_Lean_stringToMessageData(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object* v_stx_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_unsigned_to_nat(1u);
v___x_1416_ = l_Lean_Syntax_getArg(v_stx_1405_, v___x_1415_);
if (lean_obj_tag(v___x_1416_) == 1)
{
lean_object* v_kind_1417_; 
v_kind_1417_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_kind_1417_);
if (lean_obj_tag(v_kind_1417_) == 1)
{
lean_object* v_pre_1418_; 
v_pre_1418_ = lean_ctor_get(v_kind_1417_, 0);
lean_inc(v_pre_1418_);
if (lean_obj_tag(v_pre_1418_) == 1)
{
lean_object* v_pre_1419_; 
v_pre_1419_ = lean_ctor_get(v_pre_1418_, 0);
lean_inc(v_pre_1419_);
if (lean_obj_tag(v_pre_1419_) == 1)
{
lean_object* v_pre_1420_; 
v_pre_1420_ = lean_ctor_get(v_pre_1419_, 0);
lean_inc(v_pre_1420_);
if (lean_obj_tag(v_pre_1420_) == 1)
{
lean_object* v_pre_1421_; 
v_pre_1421_ = lean_ctor_get(v_pre_1420_, 0);
if (lean_obj_tag(v_pre_1421_) == 0)
{
lean_object* v_args_1422_; lean_object* v_str_1423_; lean_object* v_str_1424_; lean_object* v_str_1425_; lean_object* v_str_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_args_1422_ = lean_ctor_get(v___x_1416_, 2);
lean_inc_ref(v_args_1422_);
lean_dec_ref_known(v___x_1416_, 3);
v_str_1423_ = lean_ctor_get(v_kind_1417_, 1);
lean_inc_ref(v_str_1423_);
lean_dec_ref_known(v_kind_1417_, 2);
v_str_1424_ = lean_ctor_get(v_pre_1418_, 1);
lean_inc_ref(v_str_1424_);
lean_dec_ref_known(v_pre_1418_, 2);
v_str_1425_ = lean_ctor_get(v_pre_1419_, 1);
lean_inc_ref(v_str_1425_);
lean_dec_ref_known(v_pre_1419_, 2);
v_str_1426_ = lean_ctor_get(v_pre_1420_, 1);
lean_inc_ref(v_str_1426_);
lean_dec_ref_known(v_pre_1420_, 2);
v___x_1427_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2));
v___x_1428_ = lean_string_dec_eq(v_str_1426_, v___x_1427_);
lean_dec_ref(v_str_1426_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v_str_1425_);
lean_dec_ref(v_str_1424_);
lean_dec_ref(v_str_1423_);
lean_dec_ref(v_args_1422_);
goto v___jp_1409_;
}
else
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3));
v___x_1430_ = lean_string_dec_eq(v_str_1425_, v___x_1429_);
lean_dec_ref(v_str_1425_);
if (v___x_1430_ == 0)
{
lean_dec_ref(v_str_1424_);
lean_dec_ref(v_str_1423_);
lean_dec_ref(v_args_1422_);
goto v___jp_1409_;
}
else
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4));
v___x_1432_ = lean_string_dec_eq(v_str_1424_, v___x_1431_);
lean_dec_ref(v_str_1424_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v_str_1423_);
lean_dec_ref(v_args_1422_);
goto v___jp_1409_;
}
else
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5));
v___x_1434_ = lean_string_dec_eq(v_str_1423_, v___x_1433_);
lean_dec_ref(v_str_1423_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v_args_1422_);
goto v___jp_1409_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_array_get_size(v_args_1422_);
v___x_1436_ = lean_unsigned_to_nat(2u);
v___x_1437_ = lean_nat_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v_args_1422_);
goto v___jp_1409_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_array_fget(v_args_1422_, v___x_1438_);
lean_dec_ref(v_args_1422_);
if (lean_obj_tag(v___x_1439_) == 2)
{
lean_object* v_val_1440_; lean_object* v___x_1441_; 
lean_dec(v_stx_1405_);
v_val_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc_ref(v_val_1440_);
lean_dec_ref_known(v___x_1439_, 2);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_val_1440_);
return v___x_1441_;
}
else
{
lean_dec(v___x_1439_);
goto v___jp_1409_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1420_, 2);
lean_dec_ref_known(v_pre_1419_, 2);
lean_dec_ref_known(v_pre_1418_, 2);
lean_dec_ref_known(v_kind_1417_, 2);
lean_dec_ref_known(v___x_1416_, 3);
goto v___jp_1409_;
}
}
else
{
lean_dec_ref_known(v_pre_1419_, 2);
lean_dec(v_pre_1420_);
lean_dec_ref_known(v_pre_1418_, 2);
lean_dec_ref_known(v_kind_1417_, 2);
lean_dec_ref_known(v___x_1416_, 3);
goto v___jp_1409_;
}
}
else
{
lean_dec_ref_known(v_pre_1418_, 2);
lean_dec(v_pre_1419_);
lean_dec_ref_known(v_kind_1417_, 2);
lean_dec_ref_known(v___x_1416_, 3);
goto v___jp_1409_;
}
}
else
{
lean_dec(v_pre_1418_);
lean_dec_ref_known(v_kind_1417_, 2);
lean_dec_ref_known(v___x_1416_, 3);
goto v___jp_1409_;
}
}
else
{
lean_dec_ref_known(v___x_1416_, 3);
lean_dec(v_kind_1417_);
goto v___jp_1409_;
}
}
else
{
lean_dec(v___x_1416_);
goto v___jp_1409_;
}
v___jp_1409_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1410_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1);
lean_inc(v_stx_1405_);
v___x_1411_ = l_Lean_MessageData_ofSyntax(v_stx_1405_);
v___x_1412_ = l_Lean_indentD(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1410_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_stx_1405_, v___x_1413_, v___y_1406_, v___y_1407_);
lean_dec(v_stx_1405_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object* v_stx_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_stx_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object* v_doc_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_isVersoDocComment(v_doc_1447_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_doc_1447_, v_a_1448_, v_a_1449_);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___boxed), 4, 1);
lean_closure_set(v___x_1453_, 0, v_doc_1447_);
v___x_1454_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1453_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1485_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1485_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1485_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
if (lean_obj_tag(v_a_1455_) == 1)
{
lean_object* v_val_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_del_object(v___x_1457_);
v_val_1459_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v_a_1455_, 1);
v___x_1460_ = l_Lean_TSyntax_getVersoBlocks(v_val_1459_);
lean_dec(v_val_1459_);
v___x_1461_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = 0;
v___x_1463_ = lean_box(v___x_1462_);
v___x_1464_ = lean_alloc_closure((void*)(l_Lean_Doc_DocM_execForModule___boxed), 10, 3);
lean_closure_set(v___x_1464_, 0, lean_box(0));
lean_closure_set(v___x_1464_, 1, v___x_1461_);
lean_closure_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1464_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v_fst_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v_fst_1467_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_fst_1467_);
lean_dec(v_a_1466_);
v_fst_1468_ = lean_ctor_get(v_fst_1467_, 0);
lean_inc(v_fst_1468_);
v_snd_1469_ = lean_ctor_get(v_fst_1467_, 1);
lean_inc(v_snd_1469_);
lean_dec(v_fst_1467_);
v___f_1470_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1470_, 0, v_fst_1468_);
lean_closure_set(v___f_1470_, 1, v_snd_1469_);
v___x_1471_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_1471_, 0, v___f_1470_);
v___x_1472_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1471_, v_a_1448_, v_a_1449_);
return v___x_1472_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1465_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1465_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
lean_dec(v_a_1455_);
v___x_1481_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1481_);
v___x_1483_ = v___x_1457_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1454_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1454_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object* v_doc_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_doc_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object* v_p_1499_, lean_object* v_level_1500_, lean_object* v_part_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1500_, v_part_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object* v_p_1507_, lean_object* v_level_1508_, lean_object* v_part_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(v_p_1507_, v_level_1508_, v_part_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec(v_level_1508_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object* v_00_u03b1_1515_, lean_object* v_ref_1516_, lean_object* v_msg_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1516_, v_msg_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(v_00_u03b1_1522_, v_ref_1523_, v_msg_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v_ref_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(lean_object* v_p_1529_, lean_object* v___x_1530_, size_t v_sz_1531_, size_t v_i_1532_, lean_object* v_bs_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1530_, v_sz_1531_, v_i_1532_, v_bs_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___boxed(lean_object* v_p_1539_, lean_object* v___x_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_bs_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(v_p_1539_, v___x_1540_, v_sz_boxed_1548_, v_i_boxed_1549_, v_bs_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v___x_1540_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(lean_object* v_msgData_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1551_, v___y_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(v_msgData_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1561_, lean_object* v_msg_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1562_, v___y_1563_, v___y_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_msg_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(v_00_u03b1_1567_, v_msg_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(lean_object* v_msgData_1573_, lean_object* v_macroStack_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1573_, v_macroStack_1574_, v___y_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_msgData_1579_, lean_object* v_macroStack_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(v_msgData_1579_, v_macroStack_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v_s_1587_){
_start:
{
lean_object* v_addEntryFn_1588_; lean_object* v_importedEntries_1589_; lean_object* v_state_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
v_addEntryFn_1588_ = lean_ctor_get(v___x_1585_, 3);
lean_inc(v_addEntryFn_1588_);
lean_dec_ref(v___x_1585_);
v_importedEntries_1589_ = lean_ctor_get(v_s_1587_, 0);
v_state_1590_ = lean_ctor_get(v_s_1587_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_s_1587_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1592_ = v_s_1587_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_state_1590_);
lean_inc(v_importedEntries_1589_);
lean_dec(v_s_1587_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_state_1594_; lean_object* v___x_1596_; 
v_state_1594_ = lean_apply_2(v_addEntryFn_1588_, v_state_1590_, v___x_1586_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v_state_1594_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_importedEntries_1589_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_state_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1599_, v___x_1600_, v___y_1605_, v___y_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed(lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(v___x_1609_, v___x_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1618_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6));
v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_messages_1654_; lean_object* v_scopes_1655_; lean_object* v_usedQuotCtxts_1656_; lean_object* v_nextMacroScope_1657_; lean_object* v_maxRecDepth_1658_; lean_object* v_ngen_1659_; lean_object* v_auxDeclNGen_1660_; lean_object* v_infoState_1661_; lean_object* v_traceState_1662_; lean_object* v_snapshotTasks_1663_; lean_object* v_prevLinterStates_1664_; lean_object* v_codeQualityEntryTasks_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
lean_inc(v_x_1649_);
v___x_1673_ = l_Lean_Syntax_isOfKind(v_x_1649_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_x_1649_);
v___x_1674_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1675_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1674_, v_a_1650_, v_a_1651_);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = l_Lean_Syntax_getArg(v_x_1649_, v___x_1676_);
lean_inc(v___x_1677_);
v___x_1678_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_1676_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1677_);
v___x_1680_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v___x_1677_);
lean_dec(v_x_1649_);
v___x_1681_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1682_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1681_, v_a_1650_, v_a_1651_);
return v___x_1682_;
}
else
{
lean_object* v_docs_1683_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1743_; 
v_docs_1683_ = l_Lean_Syntax_getArg(v___x_1677_, v___x_1676_);
lean_dec(v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_docs_1683_);
v___x_1777_ = l_Lean_Syntax_isOfKind(v_docs_1683_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_docs_1683_);
lean_dec(v_x_1649_);
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1779_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1778_, v_a_1650_, v_a_1651_);
return v___x_1779_;
}
else
{
goto v___jp_1769_;
}
}
else
{
goto v___jp_1769_;
}
v___jp_1684_:
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_docs_1683_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v_env_1691_; lean_object* v_messages_1692_; lean_object* v_scopes_1693_; lean_object* v_usedQuotCtxts_1694_; lean_object* v_nextMacroScope_1695_; lean_object* v_maxRecDepth_1696_; lean_object* v_ngen_1697_; lean_object* v_auxDeclNGen_1698_; lean_object* v_infoState_1699_; lean_object* v_traceState_1700_; lean_object* v_snapshotTasks_1701_; lean_object* v_prevLinterStates_1702_; lean_object* v_codeQualityEntryTasks_1703_; lean_object* v___x_1704_; lean_object* v_toEnvExtension_1705_; lean_object* v_asyncMode_1706_; uint8_t v_logWrites_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_st_ref_take(v___y_1687_);
v_env_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc_ref(v_env_1691_);
v_messages_1692_ = lean_ctor_get(v___x_1690_, 1);
lean_inc_ref(v_messages_1692_);
v_scopes_1693_ = lean_ctor_get(v___x_1690_, 2);
lean_inc(v_scopes_1693_);
v_usedQuotCtxts_1694_ = lean_ctor_get(v___x_1690_, 3);
lean_inc(v_usedQuotCtxts_1694_);
v_nextMacroScope_1695_ = lean_ctor_get(v___x_1690_, 4);
lean_inc(v_nextMacroScope_1695_);
v_maxRecDepth_1696_ = lean_ctor_get(v___x_1690_, 5);
lean_inc(v_maxRecDepth_1696_);
v_ngen_1697_ = lean_ctor_get(v___x_1690_, 6);
lean_inc_ref(v_ngen_1697_);
v_auxDeclNGen_1698_ = lean_ctor_get(v___x_1690_, 7);
lean_inc_ref(v_auxDeclNGen_1698_);
v_infoState_1699_ = lean_ctor_get(v___x_1690_, 8);
lean_inc_ref(v_infoState_1699_);
v_traceState_1700_ = lean_ctor_get(v___x_1690_, 9);
lean_inc_ref(v_traceState_1700_);
v_snapshotTasks_1701_ = lean_ctor_get(v___x_1690_, 10);
lean_inc_ref(v_snapshotTasks_1701_);
v_prevLinterStates_1702_ = lean_ctor_get(v___x_1690_, 11);
lean_inc(v_prevLinterStates_1702_);
v_codeQualityEntryTasks_1703_ = lean_ctor_get(v___x_1690_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1703_);
lean_dec(v___x_1690_);
v___x_1704_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_1705_ = lean_ctor_get(v___x_1704_, 0);
v_asyncMode_1706_ = lean_ctor_get(v_toEnvExtension_1705_, 2);
v_logWrites_1707_ = lean_ctor_get_uint8(v_toEnvExtension_1705_, sizeof(void*)*6);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___y_1685_);
lean_ctor_set(v___x_1708_, 1, v_a_1689_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0), 3, 2);
lean_closure_set(v___f_1709_, 0, v___x_1704_);
lean_closure_set(v___f_1709_, 1, v___x_1708_);
v___x_1710_ = lean_box(0);
if (v_logWrites_1707_ == 0)
{
lean_object* v___x_1711_; 
lean_inc_ref(v_toEnvExtension_1705_);
v___x_1711_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1705_, v_env_1691_, v___f_1709_, v_asyncMode_1706_, v___x_1710_, v___x_1680_);
v_messages_1654_ = v_messages_1692_;
v_scopes_1655_ = v_scopes_1693_;
v_usedQuotCtxts_1656_ = v_usedQuotCtxts_1694_;
v_nextMacroScope_1657_ = v_nextMacroScope_1695_;
v_maxRecDepth_1658_ = v_maxRecDepth_1696_;
v_ngen_1659_ = v_ngen_1697_;
v_auxDeclNGen_1660_ = v_auxDeclNGen_1698_;
v_infoState_1661_ = v_infoState_1699_;
v_traceState_1662_ = v_traceState_1700_;
v_snapshotTasks_1663_ = v_snapshotTasks_1701_;
v_prevLinterStates_1664_ = v_prevLinterStates_1702_;
v_codeQualityEntryTasks_1665_ = v_codeQualityEntryTasks_1703_;
v___y_1666_ = v___y_1687_;
v___y_1667_ = v___x_1711_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_inc_ref_n(v_toEnvExtension_1705_, 2);
v___x_1712_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1705_, v_env_1691_);
lean_dec_ref(v_env_1691_);
v___x_1713_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1705_, v___x_1712_, v___f_1709_, v_asyncMode_1706_, v___x_1710_, v___x_1680_);
v_messages_1654_ = v_messages_1692_;
v_scopes_1655_ = v_scopes_1693_;
v_usedQuotCtxts_1656_ = v_usedQuotCtxts_1694_;
v_nextMacroScope_1657_ = v_nextMacroScope_1695_;
v_maxRecDepth_1658_ = v_maxRecDepth_1696_;
v_ngen_1659_ = v_ngen_1697_;
v_auxDeclNGen_1660_ = v_auxDeclNGen_1698_;
v_infoState_1661_ = v_infoState_1699_;
v_traceState_1662_ = v_traceState_1700_;
v_snapshotTasks_1663_ = v_snapshotTasks_1701_;
v_prevLinterStates_1664_ = v_prevLinterStates_1702_;
v_codeQualityEntryTasks_1665_ = v_codeQualityEntryTasks_1703_;
v___y_1666_ = v___y_1687_;
v___y_1667_ = v___x_1713_;
goto v___jp_1653_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v___y_1685_);
v_a_1714_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1688_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1688_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
v___jp_1722_:
{
if (v___y_1727_ == 0)
{
lean_dec(v___y_1723_);
v___y_1685_ = v___y_1725_;
v___y_1686_ = v___y_1726_;
v___y_1687_ = v___y_1724_;
goto v___jp_1684_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_docs_1683_);
v___x_1728_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1729_ = l_Lean_MessageData_ofConstName(v___y_1725_, v___x_1678_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1723_, v___x_1732_, v___y_1726_, v___y_1724_);
lean_dec(v___y_1723_);
return v___x_1733_;
}
}
v___jp_1734_:
{
lean_object* v___x_1739_; lean_object* v_env_1740_; uint8_t v___x_1741_; 
v___x_1739_ = lean_st_ref_get(v___y_1738_);
v_env_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc_ref(v_env_1740_);
lean_dec(v___x_1739_);
v___x_1741_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1740_, v___y_1736_);
if (v___x_1741_ == 0)
{
v___y_1723_ = v___y_1735_;
v___y_1724_ = v___y_1738_;
v___y_1725_ = v___y_1736_;
v___y_1726_ = v___y_1737_;
v___y_1727_ = v___x_1680_;
goto v___jp_1722_;
}
else
{
v___y_1723_ = v___y_1735_;
v___y_1724_ = v___y_1738_;
v___y_1725_ = v___y_1736_;
v___y_1726_ = v___y_1737_;
v___y_1727_ = v___x_1678_;
goto v___jp_1722_;
}
}
v___jp_1742_:
{
lean_object* v___x_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_box(0);
lean_inc(v___y_1743_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1745_, 0, v___y_1743_);
lean_closure_set(v___f_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1745_, v_a_1650_, v_a_1651_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v_env_1749_; lean_object* v___x_1750_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_n(v_a_1747_, 2);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = lean_st_ref_get(v_a_1651_);
v_env_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc_ref(v_env_1749_);
lean_dec(v___x_1748_);
v___x_1750_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1749_, v_a_1747_);
if (lean_obj_tag(v___x_1750_) == 1)
{
lean_object* v_val_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_docs_1683_);
v_val_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1753_ = l_Lean_MessageData_ofConstName(v_a_1747_, v___x_1678_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_MessageData_ofConstName(v_val_1751_, v___x_1678_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1752_);
v___x_1760_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1743_, v___x_1759_, v_a_1650_, v_a_1651_);
lean_dec(v___y_1743_);
return v___x_1760_;
}
else
{
lean_dec(v___x_1750_);
v___y_1735_ = v___y_1743_;
v___y_1736_ = v_a_1747_;
v___y_1737_ = v_a_1650_;
v___y_1738_ = v_a_1651_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v___y_1743_);
lean_dec(v_docs_1683_);
v_a_1761_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1746_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1746_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
v___jp_1769_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_unsigned_to_nat(2u);
v___x_1771_ = l_Lean_Syntax_getArg(v_x_1649_, v___x_1770_);
lean_dec(v_x_1649_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v___x_1771_);
v___x_1773_ = l_Lean_Syntax_isOfKind(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v___x_1771_);
lean_dec(v_docs_1683_);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1775_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1774_, v_a_1650_, v_a_1651_);
return v___x_1775_;
}
else
{
v___y_1743_ = v___x_1771_;
goto v___jp_1742_;
}
}
else
{
v___y_1743_ = v___x_1771_;
goto v___jp_1742_;
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v_cmd_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1677_);
v___x_1780_ = lean_unsigned_to_nat(1u);
v_cmd_1781_ = l_Lean_Syntax_getArg(v_x_1649_, v___x_1780_);
lean_dec(v_x_1649_);
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15);
v___x_1783_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_cmd_1781_, v___x_1782_, v_a_1650_, v_a_1651_);
lean_dec(v_cmd_1781_);
return v___x_1783_;
}
}
v___jp_1653_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1668_, 0, v___y_1667_);
lean_ctor_set(v___x_1668_, 1, v_messages_1654_);
lean_ctor_set(v___x_1668_, 2, v_scopes_1655_);
lean_ctor_set(v___x_1668_, 3, v_usedQuotCtxts_1656_);
lean_ctor_set(v___x_1668_, 4, v_nextMacroScope_1657_);
lean_ctor_set(v___x_1668_, 5, v_maxRecDepth_1658_);
lean_ctor_set(v___x_1668_, 6, v_ngen_1659_);
lean_ctor_set(v___x_1668_, 7, v_auxDeclNGen_1660_);
lean_ctor_set(v___x_1668_, 8, v_infoState_1661_);
lean_ctor_set(v___x_1668_, 9, v_traceState_1662_);
lean_ctor_set(v___x_1668_, 10, v_snapshotTasks_1663_);
lean_ctor_set(v___x_1668_, 11, v_prevLinterStates_1664_);
lean_ctor_set(v___x_1668_, 12, v_codeQualityEntryTasks_1665_);
v___x_1669_ = lean_st_ref_put(v___y_1666_, v___x_1668_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1800_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_1802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1803_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_1804_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_1835_ = l_Lean_addBuiltinDeclarationRanges(v___x_1833_, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0(lean_object* v___x_1838_, lean_object* v___x_1839_, lean_object* v_s_1840_){
_start:
{
lean_object* v_addEntryFn_1841_; lean_object* v_importedEntries_1842_; lean_object* v_state_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_addEntryFn_1841_ = lean_ctor_get(v___x_1838_, 3);
lean_inc(v_addEntryFn_1841_);
lean_dec_ref(v___x_1838_);
v_importedEntries_1842_ = lean_ctor_get(v_s_1840_, 0);
v_state_1843_ = lean_ctor_get(v_s_1840_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_s_1840_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v_s_1840_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_state_1843_);
lean_inc(v_importedEntries_1842_);
lean_dec(v_s_1840_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_state_1847_; lean_object* v___x_1849_; 
v_state_1847_ = lean_apply_2(v_addEntryFn_1841_, v_state_1843_, v___x_1839_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v_state_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_importedEntries_1842_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_state_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2));
v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_messages_1869_; lean_object* v_scopes_1870_; lean_object* v_usedQuotCtxts_1871_; lean_object* v_nextMacroScope_1872_; lean_object* v_maxRecDepth_1873_; lean_object* v_ngen_1874_; lean_object* v_auxDeclNGen_1875_; lean_object* v_infoState_1876_; lean_object* v_traceState_1877_; lean_object* v_snapshotTasks_1878_; lean_object* v_prevLinterStates_1879_; lean_object* v_codeQualityEntryTasks_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___x_1887_; uint8_t v___x_1888_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v_a_1893_; lean_object* v_doc_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; 
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
lean_inc(v_x_1864_);
v___x_1888_ = l_Lean_Syntax_isOfKind(v_x_1864_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v_x_1864_);
v___x_1957_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1958_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1957_, v_a_1865_, v_a_1866_);
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1959_);
v___x_1961_ = l_Lean_Syntax_isNone(v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1960_);
v___x_1963_ = l_Lean_Syntax_matchesNull(v___x_1960_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec(v___x_1960_);
lean_dec(v_x_1864_);
v___x_1964_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1965_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1964_, v_a_1865_, v_a_1866_);
return v___x_1965_;
}
else
{
lean_object* v_doc_1966_; 
v_doc_1966_ = l_Lean_Syntax_getArg(v___x_1960_, v___x_1959_);
lean_dec(v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_doc_1966_);
v___x_1970_ = l_Lean_Syntax_isOfKind(v_doc_1966_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_dec(v_doc_1966_);
lean_dec(v_x_1864_);
v___x_1971_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1972_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1971_, v_a_1865_, v_a_1866_);
return v___x_1972_;
}
else
{
goto v___jp_1967_;
}
}
else
{
goto v___jp_1967_;
}
v___jp_1967_:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_doc_1966_);
v_doc_1923_ = v___x_1968_;
v___y_1924_ = v_a_1865_;
v___y_1925_ = v_a_1866_;
goto v___jp_1922_;
}
}
}
else
{
lean_object* v___x_1973_; 
lean_dec(v___x_1960_);
v___x_1973_ = lean_box(0);
v_doc_1923_ = v___x_1973_;
v___y_1924_ = v_a_1865_;
v___y_1925_ = v_a_1866_;
goto v___jp_1922_;
}
}
v___jp_1868_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1884_, 0, v___y_1883_);
lean_ctor_set(v___x_1884_, 1, v_messages_1869_);
lean_ctor_set(v___x_1884_, 2, v_scopes_1870_);
lean_ctor_set(v___x_1884_, 3, v_usedQuotCtxts_1871_);
lean_ctor_set(v___x_1884_, 4, v_nextMacroScope_1872_);
lean_ctor_set(v___x_1884_, 5, v_maxRecDepth_1873_);
lean_ctor_set(v___x_1884_, 6, v_ngen_1874_);
lean_ctor_set(v___x_1884_, 7, v_auxDeclNGen_1875_);
lean_ctor_set(v___x_1884_, 8, v_infoState_1876_);
lean_ctor_set(v___x_1884_, 9, v_traceState_1877_);
lean_ctor_set(v___x_1884_, 10, v_snapshotTasks_1878_);
lean_ctor_set(v___x_1884_, 11, v_prevLinterStates_1879_);
lean_ctor_set(v___x_1884_, 12, v_codeQualityEntryTasks_1880_);
v___x_1885_ = lean_st_ref_put(v___y_1881_, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___y_1882_);
return v___x_1886_;
}
v___jp_1889_:
{
lean_object* v___x_1894_; lean_object* v_env_1895_; lean_object* v_messages_1896_; lean_object* v_scopes_1897_; lean_object* v_usedQuotCtxts_1898_; lean_object* v_nextMacroScope_1899_; lean_object* v_maxRecDepth_1900_; lean_object* v_ngen_1901_; lean_object* v_auxDeclNGen_1902_; lean_object* v_infoState_1903_; lean_object* v_traceState_1904_; lean_object* v_snapshotTasks_1905_; lean_object* v_prevLinterStates_1906_; lean_object* v_codeQualityEntryTasks_1907_; lean_object* v___x_1908_; lean_object* v_toEnvExtension_1909_; lean_object* v_asyncMode_1910_; uint8_t v_logWrites_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; 
v___x_1894_ = lean_st_ref_take(v___y_1890_);
v_env_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_ref(v_env_1895_);
v_messages_1896_ = lean_ctor_get(v___x_1894_, 1);
lean_inc_ref(v_messages_1896_);
v_scopes_1897_ = lean_ctor_get(v___x_1894_, 2);
lean_inc(v_scopes_1897_);
v_usedQuotCtxts_1898_ = lean_ctor_get(v___x_1894_, 3);
lean_inc(v_usedQuotCtxts_1898_);
v_nextMacroScope_1899_ = lean_ctor_get(v___x_1894_, 4);
lean_inc(v_nextMacroScope_1899_);
v_maxRecDepth_1900_ = lean_ctor_get(v___x_1894_, 5);
lean_inc(v_maxRecDepth_1900_);
v_ngen_1901_ = lean_ctor_get(v___x_1894_, 6);
lean_inc_ref(v_ngen_1901_);
v_auxDeclNGen_1902_ = lean_ctor_get(v___x_1894_, 7);
lean_inc_ref(v_auxDeclNGen_1902_);
v_infoState_1903_ = lean_ctor_get(v___x_1894_, 8);
lean_inc_ref(v_infoState_1903_);
v_traceState_1904_ = lean_ctor_get(v___x_1894_, 9);
lean_inc_ref(v_traceState_1904_);
v_snapshotTasks_1905_ = lean_ctor_get(v___x_1894_, 10);
lean_inc_ref(v_snapshotTasks_1905_);
v_prevLinterStates_1906_ = lean_ctor_get(v___x_1894_, 11);
lean_inc(v_prevLinterStates_1906_);
v_codeQualityEntryTasks_1907_ = lean_ctor_get(v___x_1894_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1907_);
lean_dec(v___x_1894_);
v___x_1908_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1909_ = lean_ctor_get(v___x_1908_, 0);
v_asyncMode_1910_ = lean_ctor_get(v_toEnvExtension_1909_, 2);
v_logWrites_1911_ = lean_ctor_get_uint8(v_toEnvExtension_1909_, sizeof(void*)*6);
v___x_1912_ = lean_box(0);
v___x_1913_ = l_Lean_TSyntax_getId(v___y_1891_);
lean_dec(v___y_1891_);
v___x_1914_ = l_Lean_TSyntax_getString(v___y_1892_);
lean_dec(v___y_1892_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_a_1893_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0), 3, 2);
lean_closure_set(v___f_1917_, 0, v___x_1908_);
lean_closure_set(v___f_1917_, 1, v___x_1916_);
v___x_1918_ = lean_box(0);
if (v_logWrites_1911_ == 0)
{
lean_object* v___x_1919_; 
lean_inc_ref(v_toEnvExtension_1909_);
v___x_1919_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1909_, v_env_1895_, v___f_1917_, v_asyncMode_1910_, v___x_1918_, v___x_1888_);
v_messages_1869_ = v_messages_1896_;
v_scopes_1870_ = v_scopes_1897_;
v_usedQuotCtxts_1871_ = v_usedQuotCtxts_1898_;
v_nextMacroScope_1872_ = v_nextMacroScope_1899_;
v_maxRecDepth_1873_ = v_maxRecDepth_1900_;
v_ngen_1874_ = v_ngen_1901_;
v_auxDeclNGen_1875_ = v_auxDeclNGen_1902_;
v_infoState_1876_ = v_infoState_1903_;
v_traceState_1877_ = v_traceState_1904_;
v_snapshotTasks_1878_ = v_snapshotTasks_1905_;
v_prevLinterStates_1879_ = v_prevLinterStates_1906_;
v_codeQualityEntryTasks_1880_ = v_codeQualityEntryTasks_1907_;
v___y_1881_ = v___y_1890_;
v___y_1882_ = v___x_1912_;
v___y_1883_ = v___x_1919_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_inc_ref_n(v_toEnvExtension_1909_, 2);
v___x_1920_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1909_, v_env_1895_);
lean_dec_ref(v_env_1895_);
v___x_1921_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1909_, v___x_1920_, v___f_1917_, v_asyncMode_1910_, v___x_1918_, v___x_1888_);
v_messages_1869_ = v_messages_1896_;
v_scopes_1870_ = v_scopes_1897_;
v_usedQuotCtxts_1871_ = v_usedQuotCtxts_1898_;
v_nextMacroScope_1872_ = v_nextMacroScope_1899_;
v_maxRecDepth_1873_ = v_maxRecDepth_1900_;
v_ngen_1874_ = v_ngen_1901_;
v_auxDeclNGen_1875_ = v_auxDeclNGen_1902_;
v_infoState_1876_ = v_infoState_1903_;
v_traceState_1877_ = v_traceState_1904_;
v_snapshotTasks_1878_ = v_snapshotTasks_1905_;
v_prevLinterStates_1879_ = v_prevLinterStates_1906_;
v_codeQualityEntryTasks_1880_ = v_codeQualityEntryTasks_1907_;
v___y_1881_ = v___y_1890_;
v___y_1882_ = v___x_1912_;
v___y_1883_ = v___x_1921_;
goto v___jp_1868_;
}
}
v___jp_1922_:
{
lean_object* v___x_1926_; lean_object* v_tag_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1926_ = lean_unsigned_to_nat(2u);
v_tag_1927_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v_tag_1927_);
v___x_1929_ = l_Lean_Syntax_isOfKind(v_tag_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec(v_tag_1927_);
lean_dec(v_doc_1923_);
lean_dec(v_x_1864_);
v___x_1930_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1931_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1930_, v___y_1924_, v___y_1925_);
return v___x_1931_;
}
else
{
lean_object* v___x_1932_; lean_object* v_user_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1932_ = lean_unsigned_to_nat(3u);
v_user_1933_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1932_);
lean_dec(v_x_1864_);
v___x_1934_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_user_1933_);
v___x_1935_ = l_Lean_Syntax_isOfKind(v_user_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_user_1933_);
lean_dec(v_tag_1927_);
lean_dec(v_doc_1923_);
v___x_1936_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1937_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1936_, v___y_1924_, v___y_1925_);
return v___x_1937_;
}
else
{
if (lean_obj_tag(v_doc_1923_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_box(0);
v___y_1890_ = v___y_1925_;
v___y_1891_ = v_tag_1927_;
v___y_1892_ = v_user_1933_;
v_a_1893_ = v___x_1938_;
goto v___jp_1889_;
}
else
{
lean_object* v_val_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1956_; 
v_val_1939_ = lean_ctor_get(v_doc_1923_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_doc_1923_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1941_ = v_doc_1923_;
v_isShared_1942_ = v_isSharedCheck_1956_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_val_1939_);
lean_dec(v_doc_1923_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1956_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; 
v___x_1943_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_val_1939_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v_a_1944_);
v___x_1946_ = v___x_1941_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
v___y_1890_ = v___y_1925_;
v___y_1891_ = v_tag_1927_;
v___y_1892_ = v_user_1933_;
v_a_1893_ = v___x_1946_;
goto v___jp_1889_;
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1941_);
lean_dec(v_user_1933_);
lean_dec(v_tag_1927_);
v_a_1948_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1943_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1987_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_1990_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_1991_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1987_, v___x_1988_, v___x_1989_, v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_2022_ = l_Lean_addBuiltinDeclarationRanges(v___x_2020_, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_2025_, lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
return v___x_2027_;
}
else
{
lean_dec_ref(v___x_2025_);
lean_inc_ref(v_x_2026_);
return v_x_2026_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2028_, v_x_2029_);
lean_dec(v_x_2029_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_2031_, lean_object* v_k_2032_, lean_object* v_t_2033_){
_start:
{
if (lean_obj_tag(v_t_2033_) == 0)
{
lean_object* v_size_2034_; lean_object* v_k_2035_; lean_object* v_v_2036_; lean_object* v_l_2037_; lean_object* v_r_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2364_; 
v_size_2034_ = lean_ctor_get(v_t_2033_, 0);
v_k_2035_ = lean_ctor_get(v_t_2033_, 1);
v_v_2036_ = lean_ctor_get(v_t_2033_, 2);
v_l_2037_ = lean_ctor_get(v_t_2033_, 3);
v_r_2038_ = lean_ctor_get(v_t_2033_, 4);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_t_2033_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2040_ = v_t_2033_;
v_isShared_2041_ = v_isSharedCheck_2364_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_r_2038_);
lean_inc(v_l_2037_);
lean_inc(v_v_2036_);
lean_inc(v_k_2035_);
lean_inc(v_size_2034_);
lean_dec(v_t_2033_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2364_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
uint8_t v___x_2042_; 
v___x_2042_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2032_, v_k_2035_);
switch(v___x_2042_)
{
case 0:
{
lean_object* v_impl_2043_; lean_object* v___x_2044_; 
lean_del_object(v___x_2040_);
lean_dec(v_size_2034_);
v_impl_2043_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2031_, v_k_2032_, v_l_2037_);
v___x_2044_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2035_, v_v_2036_, v_impl_2043_, v_r_2038_);
return v___x_2044_;
}
case 1:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec(v_k_2035_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_v_2036_);
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2031_, v___x_2045_);
lean_dec_ref_known(v___x_2045_, 1);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_del_object(v___x_2040_);
lean_dec(v_size_2034_);
lean_dec(v_k_2032_);
if (lean_obj_tag(v_l_2037_) == 0)
{
if (lean_obj_tag(v_r_2038_) == 0)
{
lean_object* v_size_2047_; lean_object* v_k_2048_; lean_object* v_v_2049_; lean_object* v_l_2050_; lean_object* v_r_2051_; lean_object* v_size_2052_; lean_object* v_k_2053_; lean_object* v_v_2054_; lean_object* v_l_2055_; lean_object* v_r_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_size_2047_ = lean_ctor_get(v_l_2037_, 0);
v_k_2048_ = lean_ctor_get(v_l_2037_, 1);
v_v_2049_ = lean_ctor_get(v_l_2037_, 2);
v_l_2050_ = lean_ctor_get(v_l_2037_, 3);
v_r_2051_ = lean_ctor_get(v_l_2037_, 4);
lean_inc(v_r_2051_);
v_size_2052_ = lean_ctor_get(v_r_2038_, 0);
v_k_2053_ = lean_ctor_get(v_r_2038_, 1);
v_v_2054_ = lean_ctor_get(v_r_2038_, 2);
v_l_2055_ = lean_ctor_get(v_r_2038_, 3);
lean_inc(v_l_2055_);
v_r_2056_ = lean_ctor_get(v_r_2038_, 4);
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_nat_dec_lt(v_size_2047_, v_size_2052_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2194_; 
lean_inc(v_l_2050_);
lean_inc(v_v_2049_);
lean_inc(v_k_2048_);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_l_2037_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; lean_object* v_unused_2198_; lean_object* v_unused_2199_; 
v_unused_2195_ = lean_ctor_get(v_l_2037_, 4);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_l_2037_, 3);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_l_2037_, 2);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_l_2037_, 1);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_l_2037_, 0);
lean_dec(v_unused_2199_);
v___x_2060_ = v_l_2037_;
v_isShared_2061_ = v_isSharedCheck_2194_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_l_2037_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2194_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v_tree_2063_; 
v___x_2062_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2048_, v_v_2049_, v_l_2050_, v_r_2051_);
v_tree_2063_ = lean_ctor_get(v___x_2062_, 2);
if (lean_obj_tag(v_tree_2063_) == 0)
{
lean_object* v_k_2064_; lean_object* v_v_2065_; lean_object* v_size_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
lean_inc_ref(v_tree_2063_);
v_k_2064_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_k_2064_);
v_v_2065_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_v_2065_);
lean_dec_ref(v___x_2062_);
v_size_2066_ = lean_ctor_get(v_tree_2063_, 0);
v___x_2067_ = lean_unsigned_to_nat(3u);
v___x_2068_ = lean_nat_mul(v___x_2067_, v_size_2066_);
v___x_2069_ = lean_nat_dec_lt(v___x_2068_, v_size_2052_);
lean_dec(v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec(v_l_2055_);
v___x_2070_ = lean_nat_add(v___x_2057_, v_size_2066_);
v___x_2071_ = lean_nat_add(v___x_2070_, v_size_2052_);
lean_dec(v___x_2070_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_r_2038_);
lean_ctor_set(v___x_2060_, 3, v_tree_2063_);
lean_ctor_set(v___x_2060_, 2, v_v_2065_);
lean_ctor_set(v___x_2060_, 1, v_k_2064_);
lean_ctor_set(v___x_2060_, 0, v___x_2071_);
v___x_2073_ = v___x_2060_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_tree_2063_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_r_2038_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
else
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2129_; 
lean_inc(v_r_2056_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
lean_inc(v_size_2052_);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_r_2038_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; lean_object* v_unused_2134_; 
v_unused_2130_ = lean_ctor_get(v_r_2038_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_r_2038_, 3);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_r_2038_, 2);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_r_2038_, 1);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_r_2038_, 0);
lean_dec(v_unused_2134_);
v___x_2076_ = v_r_2038_;
v_isShared_2077_ = v_isSharedCheck_2129_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_r_2038_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2129_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_size_2078_; lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v_l_2081_; lean_object* v_r_2082_; lean_object* v_size_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_size_2078_ = lean_ctor_get(v_l_2055_, 0);
v_k_2079_ = lean_ctor_get(v_l_2055_, 1);
v_v_2080_ = lean_ctor_get(v_l_2055_, 2);
v_l_2081_ = lean_ctor_get(v_l_2055_, 3);
v_r_2082_ = lean_ctor_get(v_l_2055_, 4);
v_size_2083_ = lean_ctor_get(v_r_2056_, 0);
v___x_2084_ = lean_unsigned_to_nat(2u);
v___x_2085_ = lean_nat_mul(v___x_2084_, v_size_2083_);
v___x_2086_ = lean_nat_dec_lt(v_size_2078_, v___x_2085_);
lean_dec(v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2114_; 
lean_inc(v_r_2082_);
lean_inc(v_l_2081_);
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_l_2055_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; 
v_unused_2115_ = lean_ctor_get(v_l_2055_, 4);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_l_2055_, 3);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_l_2055_, 2);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_l_2055_, 1);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_l_2055_, 0);
lean_dec(v_unused_2119_);
v___x_2088_ = v_l_2055_;
v_isShared_2089_ = v_isSharedCheck_2114_;
goto v_resetjp_2087_;
}
else
{
lean_dec(v_l_2055_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2114_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2104_; 
v___x_2090_ = lean_nat_add(v___x_2057_, v_size_2066_);
v___x_2091_ = lean_nat_add(v___x_2090_, v_size_2052_);
lean_dec(v_size_2052_);
if (lean_obj_tag(v_l_2081_) == 0)
{
lean_object* v_size_2112_; 
v_size_2112_ = lean_ctor_get(v_l_2081_, 0);
lean_inc(v_size_2112_);
v___y_2104_ = v_size_2112_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___y_2104_ = v___x_2113_;
goto v___jp_2103_;
}
v___jp_2092_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_nat_add(v___y_2093_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec(v___y_2093_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 4, v_r_2056_);
lean_ctor_set(v___x_2088_, 3, v_r_2082_);
lean_ctor_set(v___x_2088_, 2, v_v_2054_);
lean_ctor_set(v___x_2088_, 1, v_k_2053_);
lean_ctor_set(v___x_2088_, 0, v___x_2096_);
v___x_2098_ = v___x_2088_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_r_2082_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_r_2056_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 4, v___x_2098_);
lean_ctor_set(v___x_2076_, 3, v___y_2094_);
lean_ctor_set(v___x_2076_, 2, v_v_2080_);
lean_ctor_set(v___x_2076_, 1, v_k_2079_);
lean_ctor_set(v___x_2076_, 0, v___x_2091_);
v___x_2100_ = v___x_2076_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v___y_2094_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
v___jp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_nat_add(v___x_2090_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec(v___x_2090_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_l_2081_);
lean_ctor_set(v___x_2060_, 3, v_tree_2063_);
lean_ctor_set(v___x_2060_, 2, v_v_2065_);
lean_ctor_set(v___x_2060_, 1, v_k_2064_);
lean_ctor_set(v___x_2060_, 0, v___x_2105_);
v___x_2107_ = v___x_2060_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_tree_2063_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_l_2081_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_nat_add(v___x_2057_, v_size_2083_);
if (lean_obj_tag(v_r_2082_) == 0)
{
lean_object* v_size_2109_; 
v_size_2109_ = lean_ctor_get(v_r_2082_, 0);
lean_inc(v_size_2109_);
v___y_2093_ = v___x_2108_;
v___y_2094_ = v___x_2107_;
v___y_2095_ = v_size_2109_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___y_2093_ = v___x_2108_;
v___y_2094_ = v___x_2107_;
v___y_2095_ = v___x_2110_;
goto v___jp_2092_;
}
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2120_ = lean_nat_add(v___x_2057_, v_size_2066_);
v___x_2121_ = lean_nat_add(v___x_2120_, v_size_2052_);
lean_dec(v_size_2052_);
v___x_2122_ = lean_nat_add(v___x_2120_, v_size_2078_);
lean_dec(v___x_2120_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 4, v_l_2055_);
lean_ctor_set(v___x_2076_, 3, v_tree_2063_);
lean_ctor_set(v___x_2076_, 2, v_v_2065_);
lean_ctor_set(v___x_2076_, 1, v_k_2064_);
lean_ctor_set(v___x_2076_, 0, v___x_2122_);
v___x_2124_ = v___x_2076_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_tree_2063_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_l_2055_);
v___x_2124_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_r_2056_);
lean_ctor_set(v___x_2060_, 3, v___x_2124_);
lean_ctor_set(v___x_2060_, 2, v_v_2054_);
lean_ctor_set(v___x_2060_, 1, v_k_2053_);
lean_ctor_set(v___x_2060_, 0, v___x_2121_);
v___x_2126_ = v___x_2060_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v_r_2056_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
else
{
lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2188_; 
lean_inc(v_r_2056_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
lean_inc(v_size_2052_);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_r_2038_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2189_ = lean_ctor_get(v_r_2038_, 4);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_r_2038_, 3);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_r_2038_, 2);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_r_2038_, 1);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_2038_, 0);
lean_dec(v_unused_2193_);
v___x_2136_ = v_r_2038_;
v_isShared_2137_ = v_isSharedCheck_2188_;
goto v_resetjp_2135_;
}
else
{
lean_dec(v_r_2038_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2188_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
if (lean_obj_tag(v_l_2055_) == 0)
{
if (lean_obj_tag(v_r_2056_) == 0)
{
lean_object* v_k_2138_; lean_object* v_v_2139_; lean_object* v_size_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
lean_inc(v_tree_2063_);
v_k_2138_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_k_2138_);
v_v_2139_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_v_2139_);
lean_dec_ref(v___x_2062_);
v_size_2140_ = lean_ctor_get(v_l_2055_, 0);
v___x_2141_ = lean_nat_add(v___x_2057_, v_size_2052_);
lean_dec(v_size_2052_);
v___x_2142_ = lean_nat_add(v___x_2057_, v_size_2140_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 4, v_l_2055_);
lean_ctor_set(v___x_2136_, 3, v_tree_2063_);
lean_ctor_set(v___x_2136_, 2, v_v_2139_);
lean_ctor_set(v___x_2136_, 1, v_k_2138_);
lean_ctor_set(v___x_2136_, 0, v___x_2142_);
v___x_2144_ = v___x_2136_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_2138_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_2139_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_tree_2063_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_l_2055_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_r_2056_);
lean_ctor_set(v___x_2060_, 3, v___x_2144_);
lean_ctor_set(v___x_2060_, 2, v_v_2054_);
lean_ctor_set(v___x_2060_, 1, v_k_2053_);
lean_ctor_set(v___x_2060_, 0, v___x_2141_);
v___x_2146_ = v___x_2060_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_r_2056_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_k_2149_; lean_object* v_v_2150_; lean_object* v_k_2151_; lean_object* v_v_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_size_2052_);
v_k_2149_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_k_2149_);
v_v_2150_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_v_2150_);
lean_dec_ref(v___x_2062_);
v_k_2151_ = lean_ctor_get(v_l_2055_, 1);
v_v_2152_ = lean_ctor_get(v_l_2055_, 2);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_l_2055_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2167_ = lean_ctor_get(v_l_2055_, 4);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_l_2055_, 3);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_l_2055_, 0);
lean_dec(v_unused_2169_);
v___x_2154_ = v_l_2055_;
v_isShared_2155_ = v_isSharedCheck_2166_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_v_2152_);
lean_inc(v_k_2151_);
lean_dec(v_l_2055_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2166_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_unsigned_to_nat(3u);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 4, v_r_2056_);
lean_ctor_set(v___x_2154_, 3, v_r_2056_);
lean_ctor_set(v___x_2154_, 2, v_v_2150_);
lean_ctor_set(v___x_2154_, 1, v_k_2149_);
lean_ctor_set(v___x_2154_, 0, v___x_2057_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_2149_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_2150_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_r_2056_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_r_2056_);
v___x_2158_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 3, v_r_2056_);
lean_ctor_set(v___x_2136_, 0, v___x_2057_);
v___x_2160_ = v___x_2136_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_r_2056_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_r_2056_);
v___x_2160_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2162_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v___x_2160_);
lean_ctor_set(v___x_2060_, 3, v___x_2158_);
lean_ctor_set(v___x_2060_, 2, v_v_2152_);
lean_ctor_set(v___x_2060_, 1, v_k_2151_);
lean_ctor_set(v___x_2060_, 0, v___x_2156_);
v___x_2162_ = v___x_2060_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_2151_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_2152_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2056_) == 0)
{
lean_object* v_k_2170_; lean_object* v_v_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v_size_2052_);
v_k_2170_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_k_2170_);
v_v_2171_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_v_2171_);
lean_dec_ref(v___x_2062_);
v___x_2172_ = lean_unsigned_to_nat(3u);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 4, v_l_2055_);
lean_ctor_set(v___x_2136_, 2, v_v_2171_);
lean_ctor_set(v___x_2136_, 1, v_k_2170_);
lean_ctor_set(v___x_2136_, 0, v___x_2057_);
v___x_2174_ = v___x_2136_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_l_2055_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_l_2055_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_r_2056_);
lean_ctor_set(v___x_2060_, 3, v___x_2174_);
lean_ctor_set(v___x_2060_, 2, v_v_2054_);
lean_ctor_set(v___x_2060_, 1, v_k_2053_);
lean_ctor_set(v___x_2060_, 0, v___x_2172_);
v___x_2176_ = v___x_2060_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_r_2056_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
else
{
lean_object* v_k_2179_; lean_object* v_v_2180_; lean_object* v___x_2182_; 
v_k_2179_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_k_2179_);
v_v_2180_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_v_2180_);
lean_dec_ref(v___x_2062_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 3, v_r_2056_);
v___x_2182_ = v___x_2136_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_size_2052_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_r_2056_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_r_2056_);
v___x_2182_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = lean_unsigned_to_nat(2u);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v___x_2182_);
lean_ctor_set(v___x_2060_, 3, v_r_2056_);
lean_ctor_set(v___x_2060_, 2, v_v_2180_);
lean_ctor_set(v___x_2060_, 1, v_k_2179_);
lean_ctor_set(v___x_2060_, 0, v___x_2183_);
v___x_2185_ = v___x_2060_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_k_2179_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_v_2180_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_r_2056_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v___x_2182_);
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
}
}
}
}
else
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2352_; 
lean_inc(v_r_2056_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_r_2038_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; lean_object* v_unused_2354_; lean_object* v_unused_2355_; lean_object* v_unused_2356_; lean_object* v_unused_2357_; 
v_unused_2353_ = lean_ctor_get(v_r_2038_, 4);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_r_2038_, 3);
lean_dec(v_unused_2354_);
v_unused_2355_ = lean_ctor_get(v_r_2038_, 2);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_r_2038_, 1);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_r_2038_, 0);
lean_dec(v_unused_2357_);
v___x_2201_ = v_r_2038_;
v_isShared_2202_ = v_isSharedCheck_2352_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v_r_2038_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2352_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v_tree_2204_; 
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2053_, v_v_2054_, v_l_2055_, v_r_2056_);
v_tree_2204_ = lean_ctor_get(v___x_2203_, 2);
lean_inc(v_tree_2204_);
if (lean_obj_tag(v_tree_2204_) == 0)
{
lean_object* v_k_2205_; lean_object* v_v_2206_; lean_object* v_size_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_k_2205_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_k_2205_);
v_v_2206_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_v_2206_);
lean_dec_ref(v___x_2203_);
v_size_2207_ = lean_ctor_get(v_tree_2204_, 0);
v___x_2208_ = lean_unsigned_to_nat(3u);
v___x_2209_ = lean_nat_mul(v___x_2208_, v_size_2207_);
v___x_2210_ = lean_nat_dec_lt(v___x_2209_, v_size_2047_);
lean_dec(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_dec(v_r_2051_);
v___x_2211_ = lean_nat_add(v___x_2057_, v_size_2047_);
v___x_2212_ = lean_nat_add(v___x_2211_, v_size_2207_);
lean_dec(v___x_2211_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_tree_2204_);
lean_ctor_set(v___x_2201_, 3, v_l_2037_);
lean_ctor_set(v___x_2201_, 2, v_v_2206_);
lean_ctor_set(v___x_2201_, 1, v_k_2205_);
lean_ctor_set(v___x_2201_, 0, v___x_2212_);
v___x_2214_ = v___x_2201_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_k_2205_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_v_2206_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_l_2037_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_tree_2204_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
else
{
lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2281_; 
lean_inc(v_l_2050_);
lean_inc(v_v_2049_);
lean_inc(v_k_2048_);
lean_inc(v_size_2047_);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_l_2037_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; lean_object* v_unused_2283_; lean_object* v_unused_2284_; lean_object* v_unused_2285_; lean_object* v_unused_2286_; 
v_unused_2282_ = lean_ctor_get(v_l_2037_, 4);
lean_dec(v_unused_2282_);
v_unused_2283_ = lean_ctor_get(v_l_2037_, 3);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v_l_2037_, 2);
lean_dec(v_unused_2284_);
v_unused_2285_ = lean_ctor_get(v_l_2037_, 1);
lean_dec(v_unused_2285_);
v_unused_2286_ = lean_ctor_get(v_l_2037_, 0);
lean_dec(v_unused_2286_);
v___x_2217_ = v_l_2037_;
v_isShared_2218_ = v_isSharedCheck_2281_;
goto v_resetjp_2216_;
}
else
{
lean_dec(v_l_2037_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2281_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_size_2219_; lean_object* v_size_2220_; lean_object* v_k_2221_; lean_object* v_v_2222_; lean_object* v_l_2223_; lean_object* v_r_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v_size_2219_ = lean_ctor_get(v_l_2050_, 0);
v_size_2220_ = lean_ctor_get(v_r_2051_, 0);
v_k_2221_ = lean_ctor_get(v_r_2051_, 1);
v_v_2222_ = lean_ctor_get(v_r_2051_, 2);
v_l_2223_ = lean_ctor_get(v_r_2051_, 3);
v_r_2224_ = lean_ctor_get(v_r_2051_, 4);
v___x_2225_ = lean_unsigned_to_nat(2u);
v___x_2226_ = lean_nat_mul(v___x_2225_, v_size_2219_);
v___x_2227_ = lean_nat_dec_lt(v_size_2220_, v___x_2226_);
lean_dec(v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2265_; 
lean_inc(v_r_2224_);
lean_inc(v_l_2223_);
lean_inc(v_v_2222_);
lean_inc(v_k_2221_);
lean_del_object(v___x_2217_);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_r_2051_);
if (v_isSharedCheck_2265_ == 0)
{
lean_object* v_unused_2266_; lean_object* v_unused_2267_; lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; 
v_unused_2266_ = lean_ctor_get(v_r_2051_, 4);
lean_dec(v_unused_2266_);
v_unused_2267_ = lean_ctor_get(v_r_2051_, 3);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_r_2051_, 2);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_r_2051_, 1);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_r_2051_, 0);
lean_dec(v_unused_2270_);
v___x_2229_ = v_r_2051_;
v_isShared_2230_ = v_isSharedCheck_2265_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v_r_2051_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2265_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___x_2253_; lean_object* v___y_2255_; 
v___x_2231_ = lean_nat_add(v___x_2057_, v_size_2047_);
lean_dec(v_size_2047_);
v___x_2232_ = lean_nat_add(v___x_2231_, v_size_2207_);
lean_dec(v___x_2231_);
v___x_2253_ = lean_nat_add(v___x_2057_, v_size_2219_);
if (lean_obj_tag(v_l_2223_) == 0)
{
lean_object* v_size_2263_; 
v_size_2263_ = lean_ctor_get(v_l_2223_, 0);
lean_inc(v_size_2263_);
v___y_2255_ = v_size_2263_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___y_2255_ = v___x_2264_;
goto v___jp_2254_;
}
v___jp_2233_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_nat_add(v___y_2234_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec(v___y_2234_);
lean_inc_ref(v_tree_2204_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 4, v_tree_2204_);
lean_ctor_set(v___x_2229_, 3, v_r_2224_);
lean_ctor_set(v___x_2229_, 2, v_v_2206_);
lean_ctor_set(v___x_2229_, 1, v_k_2205_);
lean_ctor_set(v___x_2229_, 0, v___x_2237_);
v___x_2239_ = v___x_2229_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2205_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2206_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_r_2224_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_tree_2204_);
v___x_2239_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_isSharedCheck_2246_ = !lean_is_exclusive(v_tree_2204_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; lean_object* v_unused_2248_; lean_object* v_unused_2249_; lean_object* v_unused_2250_; lean_object* v_unused_2251_; 
v_unused_2247_ = lean_ctor_get(v_tree_2204_, 4);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_tree_2204_, 3);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_tree_2204_, 2);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_tree_2204_, 1);
lean_dec(v_unused_2250_);
v_unused_2251_ = lean_ctor_get(v_tree_2204_, 0);
lean_dec(v_unused_2251_);
v___x_2241_ = v_tree_2204_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v_tree_2204_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v___x_2239_);
lean_ctor_set(v___x_2241_, 3, v___y_2235_);
lean_ctor_set(v___x_2241_, 2, v_v_2222_);
lean_ctor_set(v___x_2241_, 1, v_k_2221_);
lean_ctor_set(v___x_2241_, 0, v___x_2232_);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_k_2221_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_v_2222_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v___y_2235_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v___x_2239_);
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
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_nat_add(v___x_2253_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec(v___x_2253_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_l_2223_);
lean_ctor_set(v___x_2201_, 3, v_l_2050_);
lean_ctor_set(v___x_2201_, 2, v_v_2049_);
lean_ctor_set(v___x_2201_, 1, v_k_2048_);
lean_ctor_set(v___x_2201_, 0, v___x_2256_);
v___x_2258_ = v___x_2201_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_k_2048_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_v_2049_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_l_2050_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_l_2223_);
v___x_2258_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_nat_add(v___x_2057_, v_size_2207_);
if (lean_obj_tag(v_r_2224_) == 0)
{
lean_object* v_size_2260_; 
v_size_2260_ = lean_ctor_get(v_r_2224_, 0);
lean_inc(v_size_2260_);
v___y_2234_ = v___x_2259_;
v___y_2235_ = v___x_2258_;
v___y_2236_ = v_size_2260_;
goto v___jp_2233_;
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_unsigned_to_nat(0u);
v___y_2234_ = v___x_2259_;
v___y_2235_ = v___x_2258_;
v___y_2236_ = v___x_2261_;
goto v___jp_2233_;
}
}
}
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2271_ = lean_nat_add(v___x_2057_, v_size_2047_);
lean_dec(v_size_2047_);
v___x_2272_ = lean_nat_add(v___x_2271_, v_size_2207_);
lean_dec(v___x_2271_);
v___x_2273_ = lean_nat_add(v___x_2057_, v_size_2207_);
v___x_2274_ = lean_nat_add(v___x_2273_, v_size_2220_);
lean_dec(v___x_2273_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_tree_2204_);
lean_ctor_set(v___x_2201_, 3, v_r_2051_);
lean_ctor_set(v___x_2201_, 2, v_v_2206_);
lean_ctor_set(v___x_2201_, 1, v_k_2205_);
lean_ctor_set(v___x_2201_, 0, v___x_2274_);
v___x_2276_ = v___x_2201_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_k_2205_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_v_2206_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_r_2051_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_tree_2204_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 4, v___x_2276_);
lean_ctor_set(v___x_2217_, 0, v___x_2272_);
v___x_2278_ = v___x_2217_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_k_2048_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_v_2049_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_l_2050_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2050_) == 0)
{
lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2310_; 
lean_inc_ref(v_l_2050_);
lean_inc(v_v_2049_);
lean_inc(v_k_2048_);
lean_inc(v_size_2047_);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_l_2037_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2311_ = lean_ctor_get(v_l_2037_, 4);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_l_2037_, 3);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_l_2037_, 2);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_l_2037_, 1);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_l_2037_, 0);
lean_dec(v_unused_2315_);
v___x_2288_ = v_l_2037_;
v_isShared_2289_ = v_isSharedCheck_2310_;
goto v_resetjp_2287_;
}
else
{
lean_dec(v_l_2037_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2310_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
if (lean_obj_tag(v_r_2051_) == 0)
{
lean_object* v_k_2290_; lean_object* v_v_2291_; lean_object* v_size_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v_k_2290_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_k_2290_);
v_v_2291_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_v_2291_);
lean_dec_ref(v___x_2203_);
v_size_2292_ = lean_ctor_get(v_r_2051_, 0);
v___x_2293_ = lean_nat_add(v___x_2057_, v_size_2047_);
lean_dec(v_size_2047_);
v___x_2294_ = lean_nat_add(v___x_2057_, v_size_2292_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_tree_2204_);
lean_ctor_set(v___x_2201_, 3, v_r_2051_);
lean_ctor_set(v___x_2201_, 2, v_v_2291_);
lean_ctor_set(v___x_2201_, 1, v_k_2290_);
lean_ctor_set(v___x_2201_, 0, v___x_2294_);
v___x_2296_ = v___x_2201_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_r_2051_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_tree_2204_);
v___x_2296_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2298_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2296_);
lean_ctor_set(v___x_2288_, 0, v___x_2293_);
v___x_2298_ = v___x_2288_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_k_2048_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_v_2049_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_l_2050_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v_k_2301_; lean_object* v_v_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec(v_size_2047_);
v_k_2301_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_k_2301_);
v_v_2302_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_v_2302_);
lean_dec_ref(v___x_2203_);
v___x_2303_ = lean_unsigned_to_nat(3u);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_r_2051_);
lean_ctor_set(v___x_2201_, 3, v_r_2051_);
lean_ctor_set(v___x_2201_, 2, v_v_2302_);
lean_ctor_set(v___x_2201_, 1, v_k_2301_);
lean_ctor_set(v___x_2201_, 0, v___x_2057_);
v___x_2305_ = v___x_2201_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2301_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2302_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_r_2051_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_r_2051_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2305_);
lean_ctor_set(v___x_2288_, 0, v___x_2303_);
v___x_2307_ = v___x_2288_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_2048_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_2049_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_l_2050_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2051_) == 0)
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2340_; 
lean_inc(v_l_2050_);
lean_inc(v_v_2049_);
lean_inc(v_k_2048_);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_l_2037_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; lean_object* v_unused_2342_; lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; 
v_unused_2341_ = lean_ctor_get(v_l_2037_, 4);
lean_dec(v_unused_2341_);
v_unused_2342_ = lean_ctor_get(v_l_2037_, 3);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_l_2037_, 2);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_l_2037_, 1);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_l_2037_, 0);
lean_dec(v_unused_2345_);
v___x_2317_ = v_l_2037_;
v_isShared_2318_ = v_isSharedCheck_2340_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v_l_2037_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2340_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v_k_2319_; lean_object* v_v_2320_; lean_object* v_k_2321_; lean_object* v_v_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2336_; 
v_k_2319_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_k_2319_);
v_v_2320_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_v_2320_);
lean_dec_ref(v___x_2203_);
v_k_2321_ = lean_ctor_get(v_r_2051_, 1);
v_v_2322_ = lean_ctor_get(v_r_2051_, 2);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_r_2051_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; lean_object* v_unused_2338_; lean_object* v_unused_2339_; 
v_unused_2337_ = lean_ctor_get(v_r_2051_, 4);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_r_2051_, 3);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_2051_, 0);
lean_dec(v_unused_2339_);
v___x_2324_ = v_r_2051_;
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_v_2322_);
lean_inc(v_k_2321_);
lean_dec(v_r_2051_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = lean_unsigned_to_nat(3u);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 4, v_l_2050_);
lean_ctor_set(v___x_2324_, 3, v_l_2050_);
lean_ctor_set(v___x_2324_, 2, v_v_2049_);
lean_ctor_set(v___x_2324_, 1, v_k_2048_);
lean_ctor_set(v___x_2324_, 0, v___x_2057_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2048_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2049_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2050_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_l_2050_);
v___x_2328_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_l_2050_);
lean_ctor_set(v___x_2201_, 3, v_l_2050_);
lean_ctor_set(v___x_2201_, 2, v_v_2320_);
lean_ctor_set(v___x_2201_, 1, v_k_2319_);
lean_ctor_set(v___x_2201_, 0, v___x_2057_);
v___x_2330_ = v___x_2201_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2319_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2320_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_l_2050_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_l_2050_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v___x_2330_);
lean_ctor_set(v___x_2317_, 3, v___x_2328_);
lean_ctor_set(v___x_2317_, 2, v_v_2322_);
lean_ctor_set(v___x_2317_, 1, v_k_2321_);
lean_ctor_set(v___x_2317_, 0, v___x_2326_);
v___x_2332_ = v___x_2317_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2322_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v___x_2330_);
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
else
{
lean_object* v_k_2346_; lean_object* v_v_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v_k_2346_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_k_2346_);
v_v_2347_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_v_2347_);
lean_dec_ref(v___x_2203_);
v___x_2348_ = lean_unsigned_to_nat(2u);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_r_2051_);
lean_ctor_set(v___x_2201_, 3, v_l_2037_);
lean_ctor_set(v___x_2201_, 2, v_v_2347_);
lean_ctor_set(v___x_2201_, 1, v_k_2346_);
lean_ctor_set(v___x_2201_, 0, v___x_2348_);
v___x_2350_ = v___x_2201_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_k_2346_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_v_2347_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_l_2037_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_r_2051_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
}
else
{
return v_l_2037_;
}
}
else
{
return v_r_2038_;
}
}
else
{
lean_object* v_val_2358_; lean_object* v___x_2360_; 
v_val_2358_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2358_);
lean_dec_ref_known(v___x_2046_, 1);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 2, v_val_2358_);
lean_ctor_set(v___x_2040_, 1, v_k_2032_);
v___x_2360_ = v___x_2040_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_size_2034_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_k_2032_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_val_2358_);
lean_ctor_set(v_reuseFailAlloc_2361_, 3, v_l_2037_);
lean_ctor_set(v_reuseFailAlloc_2361_, 4, v_r_2038_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
default: 
{
lean_object* v_impl_2362_; lean_object* v___x_2363_; 
lean_del_object(v___x_2040_);
lean_dec(v_size_2034_);
v_impl_2362_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2031_, v_k_2032_, v_r_2038_);
v___x_2363_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2035_, v_v_2036_, v_l_2037_, v_impl_2362_);
return v___x_2363_;
}
}
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2031_, v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_dec(v_k_2032_);
return v_t_2033_;
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_val_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v_k_2032_);
lean_ctor_set(v___x_2369_, 2, v_val_2367_);
lean_ctor_set(v___x_2369_, 3, v_t_2033_);
lean_ctor_set(v___x_2369_, 4, v_t_2033_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2370_, lean_object* v_i_2371_, lean_object* v_k_2372_){
_start:
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = lean_array_get_size(v_keys_2370_);
v___x_2374_ = lean_nat_dec_lt(v_i_2371_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_dec(v_i_2371_);
return v___x_2374_;
}
else
{
lean_object* v_k_x27_2375_; uint8_t v___x_2376_; 
v_k_x27_2375_ = lean_array_fget_borrowed(v_keys_2370_, v_i_2371_);
v___x_2376_ = lean_name_eq(v_k_2372_, v_k_x27_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_nat_add(v_i_2371_, v___x_2377_);
lean_dec(v_i_2371_);
v_i_2371_ = v___x_2378_;
goto _start;
}
else
{
lean_dec(v_i_2371_);
return v___x_2374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2380_, lean_object* v_i_2381_, lean_object* v_k_2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2380_, v_i_2381_, v_k_2382_);
lean_dec(v_k_2382_);
lean_dec_ref(v_keys_2380_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_2385_, size_t v_x_2386_, lean_object* v_x_2387_){
_start:
{
if (lean_obj_tag(v_x_2385_) == 0)
{
lean_object* v_es_2388_; lean_object* v___x_2389_; size_t v___x_2390_; size_t v___x_2391_; lean_object* v_j_2392_; lean_object* v___x_2393_; 
v_es_2388_ = lean_ctor_get(v_x_2385_, 0);
v___x_2389_ = lean_box(2);
v___x_2390_ = ((size_t)31ULL);
v___x_2391_ = lean_usize_land(v_x_2386_, v___x_2390_);
v_j_2392_ = lean_usize_to_nat(v___x_2391_);
v___x_2393_ = lean_array_get_borrowed(v___x_2389_, v_es_2388_, v_j_2392_);
lean_dec(v_j_2392_);
switch(lean_obj_tag(v___x_2393_))
{
case 0:
{
lean_object* v_key_2394_; uint8_t v___x_2395_; 
v_key_2394_ = lean_ctor_get(v___x_2393_, 0);
v___x_2395_ = lean_name_eq(v_x_2387_, v_key_2394_);
return v___x_2395_;
}
case 1:
{
lean_object* v_node_2396_; size_t v___x_2397_; size_t v___x_2398_; 
v_node_2396_ = lean_ctor_get(v___x_2393_, 0);
v___x_2397_ = ((size_t)5ULL);
v___x_2398_ = lean_usize_shift_right(v_x_2386_, v___x_2397_);
v_x_2385_ = v_node_2396_;
v_x_2386_ = v___x_2398_;
goto _start;
}
default: 
{
uint8_t v___x_2400_; 
v___x_2400_ = 0;
return v___x_2400_;
}
}
}
else
{
lean_object* v_ks_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v_ks_2401_ = lean_ctor_get(v_x_2385_, 0);
v___x_2402_ = lean_unsigned_to_nat(0u);
v___x_2403_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_2401_, v___x_2402_, v_x_2387_);
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
size_t v_x_3827__boxed_2407_; uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_x_3827__boxed_2407_ = lean_unbox_usize(v_x_2405_);
lean_dec(v_x_2405_);
v_res_2408_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2404_, v_x_3827__boxed_2407_, v_x_2406_);
lean_dec(v_x_2406_);
lean_dec_ref(v_x_2404_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
uint64_t v___y_2413_; 
if (lean_obj_tag(v_x_2411_) == 0)
{
uint64_t v___x_2416_; 
v___x_2416_ = 1723ULL;
v___y_2413_ = v___x_2416_;
goto v___jp_2412_;
}
else
{
uint64_t v_hash_2417_; 
v_hash_2417_ = lean_ctor_get_uint64(v_x_2411_, sizeof(void*)*2);
v___y_2413_ = v_hash_2417_;
goto v___jp_2412_;
}
v___jp_2412_:
{
size_t v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = lean_uint64_to_usize(v___y_2413_);
v___x_2415_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2410_, v___x_2414_, v_x_2411_);
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_2418_, lean_object* v_x_2419_){
_start:
{
uint8_t v_res_2420_; lean_object* v_r_2421_; 
v_res_2420_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2418_, v_x_2419_);
lean_dec(v_x_2419_);
lean_dec_ref(v_x_2418_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_2422_, lean_object* v_a_2423_, uint8_t v___x_2424_, lean_object* v_x_2425_, lean_object* v_____s_2426_){
_start:
{
lean_object* v_fst_2427_; lean_object* v_kinds_2428_; uint8_t v___x_2429_; 
v_fst_2427_ = lean_ctor_get(v_x_2425_, 0);
lean_inc(v_fst_2427_);
lean_dec_ref(v_x_2425_);
v_kinds_2428_ = lean_ctor_get(v_tactics_2422_, 1);
v___x_2429_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_2428_, v_fst_2427_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec(v_fst_2427_);
lean_dec(v_a_2423_);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_____s_2426_);
return v___x_2430_;
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = l_Lean_Name_toString(v_a_2423_, v___x_2424_);
v___x_2432_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2431_, v_fst_2427_, v_____s_2426_);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_2434_, lean_object* v_a_2435_, lean_object* v___x_2436_, lean_object* v_x_2437_, lean_object* v_____s_2438_){
_start:
{
uint8_t v___x_3883__boxed_2439_; lean_object* v_res_2440_; 
v___x_3883__boxed_2439_ = lean_unbox(v___x_2436_);
v_res_2440_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2434_, v_a_2435_, v___x_3883__boxed_2439_, v_x_2437_, v_____s_2438_);
lean_dec_ref(v_tactics_2434_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_2441_, lean_object* v_keys_2442_, lean_object* v_vals_2443_, lean_object* v_i_2444_, lean_object* v_acc_2445_){
_start:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = lean_array_get_size(v_keys_2442_);
v___x_2447_ = lean_nat_dec_lt(v_i_2444_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec(v_i_2444_);
lean_dec_ref(v_f_2441_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_acc_2445_);
return v___x_2448_;
}
else
{
lean_object* v_k_2449_; lean_object* v_v_2450_; lean_object* v___x_2451_; 
v_k_2449_ = lean_array_fget_borrowed(v_keys_2442_, v_i_2444_);
v_v_2450_ = lean_array_fget_borrowed(v_vals_2443_, v_i_2444_);
lean_inc_ref(v_f_2441_);
lean_inc(v_v_2450_);
lean_inc(v_k_2449_);
v___x_2451_ = lean_apply_3(v_f_2441_, v_acc_2445_, v_k_2449_, v_v_2450_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec(v_i_2444_);
lean_dec_ref(v_f_2441_);
return v___x_2451_;
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = lean_nat_add(v_i_2444_, v___x_2453_);
lean_dec(v_i_2444_);
v_i_2444_ = v___x_2454_;
v_acc_2445_ = v_a_2452_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_2456_, lean_object* v_keys_2457_, lean_object* v_vals_2458_, lean_object* v_i_2459_, lean_object* v_acc_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2456_, v_keys_2457_, v_vals_2458_, v_i_2459_, v_acc_2460_);
lean_dec_ref(v_vals_2458_);
lean_dec_ref(v_keys_2457_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_2462_, lean_object* v_as_2463_, size_t v_i_2464_, size_t v_stop_2465_, lean_object* v_b_2466_){
_start:
{
lean_object* v_a_2468_; lean_object* v___y_2473_; uint8_t v___x_2475_; 
v___x_2475_ = lean_usize_dec_eq(v_i_2464_, v_stop_2465_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_array_uget_borrowed(v_as_2463_, v_i_2464_);
switch(lean_obj_tag(v___x_2476_))
{
case 0:
{
lean_object* v_key_2477_; lean_object* v_val_2478_; lean_object* v___x_2479_; 
v_key_2477_ = lean_ctor_get(v___x_2476_, 0);
v_val_2478_ = lean_ctor_get(v___x_2476_, 1);
lean_inc_ref(v_f_2462_);
lean_inc(v_val_2478_);
lean_inc(v_key_2477_);
v___x_2479_ = lean_apply_3(v_f_2462_, v_b_2466_, v_key_2477_, v_val_2478_);
v___y_2473_ = v___x_2479_;
goto v___jp_2472_;
}
case 1:
{
lean_object* v_node_2480_; lean_object* v___x_2481_; 
v_node_2480_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_node_2480_);
lean_inc_ref(v_f_2462_);
v___x_2481_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2462_, v_node_2480_, v_b_2466_);
v___y_2473_ = v___x_2481_;
goto v___jp_2472_;
}
default: 
{
v_a_2468_ = v_b_2466_;
goto v___jp_2467_;
}
}
}
else
{
lean_object* v___x_2482_; 
lean_dec_ref(v_f_2462_);
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_b_2466_);
return v___x_2482_;
}
v___jp_2467_:
{
size_t v___x_2469_; size_t v___x_2470_; 
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_add(v_i_2464_, v___x_2469_);
v_i_2464_ = v___x_2470_;
v_b_2466_ = v_a_2468_;
goto _start;
}
v___jp_2472_:
{
if (lean_obj_tag(v___y_2473_) == 0)
{
lean_dec_ref(v_f_2462_);
return v___y_2473_;
}
else
{
lean_object* v_a_2474_; 
v_a_2474_ = lean_ctor_get(v___y_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___y_2473_, 1);
v_a_2468_ = v_a_2474_;
goto v___jp_2467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_){
_start:
{
if (lean_obj_tag(v_x_2484_) == 0)
{
lean_object* v_es_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2499_; 
v_es_2486_ = lean_ctor_get(v_x_2484_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2488_ = v_x_2484_;
v_isShared_2489_ = v_isSharedCheck_2499_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_es_2486_);
lean_dec(v_x_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2499_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2490_ = lean_unsigned_to_nat(0u);
v___x_2491_ = lean_array_get_size(v_es_2486_);
v___x_2492_ = lean_nat_dec_lt(v___x_2490_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v_es_2486_);
lean_dec_ref(v_f_2483_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
lean_ctor_set(v___x_2488_, 0, v_x_2485_);
v___x_2494_ = v___x_2488_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_x_2485_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
else
{
size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; 
lean_del_object(v___x_2488_);
v___x_2496_ = ((size_t)0ULL);
v___x_2497_ = lean_usize_of_nat(v___x_2491_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2483_, v_es_2486_, v___x_2496_, v___x_2497_, v_x_2485_);
lean_dec_ref(v_es_2486_);
return v___x_2498_;
}
}
}
else
{
lean_object* v_ks_2500_; lean_object* v_vs_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_ks_2500_ = lean_ctor_get(v_x_2484_, 0);
lean_inc_ref(v_ks_2500_);
v_vs_2501_ = lean_ctor_get(v_x_2484_, 1);
lean_inc_ref(v_vs_2501_);
lean_dec_ref_known(v_x_2484_, 2);
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2483_, v_ks_2500_, v_vs_2501_, v___x_2502_, v_x_2485_);
lean_dec_ref(v_vs_2501_);
lean_dec_ref(v_ks_2500_);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_2504_, lean_object* v_as_2505_, lean_object* v_i_2506_, lean_object* v_stop_2507_, lean_object* v_b_2508_){
_start:
{
size_t v_i_boxed_2509_; size_t v_stop_boxed_2510_; lean_object* v_res_2511_; 
v_i_boxed_2509_ = lean_unbox_usize(v_i_2506_);
lean_dec(v_i_2506_);
v_stop_boxed_2510_ = lean_unbox_usize(v_stop_2507_);
lean_dec(v_stop_2507_);
v_res_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2504_, v_as_2505_, v_i_boxed_2509_, v_stop_boxed_2510_, v_b_2508_);
lean_dec_ref(v_as_2505_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_2512_, lean_object* v_s_2513_, lean_object* v_a_2514_, lean_object* v_b_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2514_);
lean_ctor_set(v___x_2516_, 1, v_b_2515_);
v___x_2517_ = lean_apply_2(v_f_2512_, v___x_2516_, v_s_2513_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_2534_, lean_object* v_init_2535_, lean_object* v_f_2536_){
_start:
{
lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; 
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2537_, 0, v_f_2536_);
lean_inc_ref(v_map_2534_);
v___x_2538_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_2537_, v_map_2534_, v_init_2535_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
return v_a_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_2540_, lean_object* v_init_2541_, lean_object* v_f_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2540_, v_init_2541_, v_f_2542_);
lean_dec_ref(v_map_2540_);
return v_res_2543_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_2546_, lean_object* v_a_2547_, uint8_t v___x_2548_, lean_object* v_as_x27_2549_, lean_object* v_b_2550_){
_start:
{
if (lean_obj_tag(v_as_x27_2549_) == 0)
{
lean_dec(v_a_2547_);
lean_dec_ref(v_tactics_2546_);
return v_b_2550_;
}
else
{
lean_object* v_head_2551_; lean_object* v_fst_2552_; lean_object* v_info_2553_; lean_object* v_tail_2554_; lean_object* v_collectKinds_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_head_2551_ = lean_ctor_get(v_as_x27_2549_, 0);
v_fst_2552_ = lean_ctor_get(v_head_2551_, 0);
v_info_2553_ = lean_ctor_get(v_fst_2552_, 0);
v_tail_2554_ = lean_ctor_get(v_as_x27_2549_, 1);
v_collectKinds_2555_ = lean_ctor_get(v_info_2553_, 1);
v___x_2556_ = lean_box(v___x_2548_);
lean_inc(v_a_2547_);
lean_inc_ref(v_tactics_2546_);
v___f_2557_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2557_, 0, v_tactics_2546_);
lean_closure_set(v___f_2557_, 1, v_a_2547_);
lean_closure_set(v___f_2557_, 2, v___x_2556_);
v___x_2558_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_2555_);
v___x_2559_ = lean_apply_1(v_collectKinds_2555_, v___x_2558_);
v___x_2560_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_2559_, v_b_2550_, v___f_2557_);
lean_dec_ref(v___x_2559_);
v_as_x27_2549_ = v_tail_2554_;
v_b_2550_ = v___x_2560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_2562_, lean_object* v_a_2563_, lean_object* v___x_2564_, lean_object* v_as_x27_2565_, lean_object* v_b_2566_){
_start:
{
uint8_t v___x_4042__boxed_2567_; lean_object* v_res_2568_; 
v___x_4042__boxed_2567_ = lean_unbox(v___x_2564_);
v_res_2568_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2562_, v_a_2563_, v___x_4042__boxed_2567_, v_as_x27_2565_, v_b_2566_);
lean_dec(v_as_x27_2565_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_2571_, lean_object* v_init_2572_, lean_object* v_x_2573_){
_start:
{
if (lean_obj_tag(v_x_2573_) == 0)
{
lean_object* v_k_2574_; lean_object* v_v_2575_; lean_object* v_l_2576_; lean_object* v_r_2577_; lean_object* v___x_2578_; lean_object* v_a_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v_k_2574_ = lean_ctor_get(v_x_2573_, 1);
lean_inc(v_k_2574_);
v_v_2575_ = lean_ctor_get(v_x_2573_, 2);
lean_inc(v_v_2575_);
v_l_2576_ = lean_ctor_get(v_x_2573_, 3);
lean_inc(v_l_2576_);
v_r_2577_ = lean_ctor_get(v_x_2573_, 4);
lean_inc(v_r_2577_);
lean_dec_ref_known(v_x_2573_, 5);
lean_inc_ref(v_tactics_2571_);
v___x_2578_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2571_, v_init_2572_, v_l_2576_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v___x_2580_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0));
v___x_2581_ = lean_name_eq(v_k_2574_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
lean_inc(v_a_2579_);
lean_dec_ref(v___x_2578_);
lean_inc_ref(v_tactics_2571_);
v___x_2582_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2571_, v_k_2574_, v___x_2581_, v_v_2575_, v_a_2579_);
lean_dec(v_v_2575_);
v_init_2572_ = v___x_2582_;
v_x_2573_ = v_r_2577_;
goto _start;
}
else
{
lean_object* v_a_2584_; 
lean_dec(v_v_2575_);
lean_dec(v_k_2574_);
v_a_2584_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2578_);
v_init_2572_ = v_a_2584_;
v_x_2573_ = v_r_2577_;
goto _start;
}
}
else
{
lean_object* v___x_2586_; 
lean_dec_ref(v_tactics_2571_);
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_init_2572_);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_2587_, lean_object* v_table_2588_, lean_object* v_firsts_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v_a_2591_; 
v___x_2590_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2587_, v_firsts_2589_, v_table_2588_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
return v_a_2591_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_){
_start:
{
uint8_t v___x_2595_; 
v___x_2595_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2593_, v_x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_){
_start:
{
uint8_t v_res_2599_; lean_object* v_r_2600_; 
v_res_2599_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_2596_, v_x_2597_, v_x_2598_);
lean_dec(v_x_2598_);
lean_dec_ref(v_x_2597_);
v_r_2600_ = lean_box(v_res_2599_);
return v_r_2600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_2601_, lean_object* v_k_2602_, lean_object* v_t_2603_, lean_object* v_hl_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2601_, v_k_2602_, v_t_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_map_2608_, lean_object* v_init_2609_, lean_object* v_f_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2608_, v_init_2609_, v_f_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_2612_, lean_object* v_00_u03b2_2613_, lean_object* v_map_2614_, lean_object* v_init_2615_, lean_object* v_f_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_2612_, v_00_u03b2_2613_, v_map_2614_, v_init_2615_, v_f_2616_);
lean_dec_ref(v_map_2614_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_2618_, lean_object* v_a_2619_, uint8_t v___x_2620_, lean_object* v_as_2621_, lean_object* v_as_x27_2622_, lean_object* v_b_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2618_, v_a_2619_, v___x_2620_, v_as_x27_2622_, v_b_2623_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_2626_, lean_object* v_a_2627_, lean_object* v___x_2628_, lean_object* v_as_2629_, lean_object* v_as_x27_2630_, lean_object* v_b_2631_, lean_object* v_a_2632_){
_start:
{
uint8_t v___x_4122__boxed_2633_; lean_object* v_res_2634_; 
v___x_4122__boxed_2633_ = lean_unbox(v___x_2628_);
v_res_2634_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2626_, v_a_2627_, v___x_4122__boxed_2633_, v_as_2629_, v_as_x27_2630_, v_b_2631_, v_a_2632_);
lean_dec(v_as_x27_2630_);
lean_dec(v_as_2629_);
return v_res_2634_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_2635_, lean_object* v_x_2636_, size_t v_x_2637_, lean_object* v_x_2638_){
_start:
{
uint8_t v___x_2639_; 
v___x_2639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2636_, v_x_2637_, v_x_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_){
_start:
{
size_t v_x_4131__boxed_2644_; uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_x_4131__boxed_2644_ = lean_unbox_usize(v_x_2642_);
lean_dec(v_x_2642_);
v_res_2645_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_2640_, v_x_2641_, v_x_4131__boxed_2644_, v_x_2643_);
lean_dec(v_x_2643_);
lean_dec_ref(v_x_2641_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_2647_, lean_object* v_f_2648_, lean_object* v_init_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2648_, v_map_2647_, v_init_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_2651_, lean_object* v_00_u03c3_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_map_2654_, lean_object* v_f_2655_, lean_object* v_init_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2655_, v_map_2654_, v_init_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2658_, lean_object* v_keys_2659_, lean_object* v_vals_2660_, lean_object* v_heq_2661_, lean_object* v_i_2662_, lean_object* v_k_2663_){
_start:
{
uint8_t v___x_2664_; 
v___x_2664_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2659_, v_i_2662_, v_k_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2665_, lean_object* v_keys_2666_, lean_object* v_vals_2667_, lean_object* v_heq_2668_, lean_object* v_i_2669_, lean_object* v_k_2670_){
_start:
{
uint8_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_2665_, v_keys_2666_, v_vals_2667_, v_heq_2668_, v_i_2669_, v_k_2670_);
lean_dec(v_k_2670_);
lean_dec_ref(v_vals_2667_);
lean_dec_ref(v_keys_2666_);
v_r_2672_ = lean_box(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_2673_, lean_object* v_00_u03c3_2674_, lean_object* v_00_u03b1_2675_, lean_object* v_00_u03b2_2676_, lean_object* v_f_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2677_, v_x_2678_, v_x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_2681_, lean_object* v_00_u03b2_2682_, lean_object* v_00_u03c3_2683_, lean_object* v_00_u03c3_2684_, lean_object* v_f_2685_, lean_object* v_as_2686_, size_t v_i_2687_, size_t v_stop_2688_, lean_object* v_b_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2685_, v_as_2686_, v_i_2687_, v_stop_2688_, v_b_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2691_, lean_object* v_00_u03b2_2692_, lean_object* v_00_u03c3_2693_, lean_object* v_00_u03c3_2694_, lean_object* v_f_2695_, lean_object* v_as_2696_, lean_object* v_i_2697_, lean_object* v_stop_2698_, lean_object* v_b_2699_){
_start:
{
size_t v_i_boxed_2700_; size_t v_stop_boxed_2701_; lean_object* v_res_2702_; 
v_i_boxed_2700_ = lean_unbox_usize(v_i_2697_);
lean_dec(v_i_2697_);
v_stop_boxed_2701_ = lean_unbox_usize(v_stop_2698_);
lean_dec(v_stop_2698_);
v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_2691_, v_00_u03b2_2692_, v_00_u03c3_2693_, v_00_u03c3_2694_, v_f_2695_, v_as_2696_, v_i_boxed_2700_, v_stop_boxed_2701_, v_b_2699_);
lean_dec_ref(v_as_2696_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_2703_, lean_object* v_00_u03c3_2704_, lean_object* v_00_u03b1_2705_, lean_object* v_00_u03b2_2706_, lean_object* v_f_2707_, lean_object* v_keys_2708_, lean_object* v_vals_2709_, lean_object* v_heq_2710_, lean_object* v_i_2711_, lean_object* v_acc_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2707_, v_keys_2708_, v_vals_2709_, v_i_2711_, v_acc_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_2714_, lean_object* v_00_u03c3_2715_, lean_object* v_00_u03b1_2716_, lean_object* v_00_u03b2_2717_, lean_object* v_f_2718_, lean_object* v_keys_2719_, lean_object* v_vals_2720_, lean_object* v_heq_2721_, lean_object* v_i_2722_, lean_object* v_acc_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_2714_, v_00_u03c3_2715_, v_00_u03b1_2716_, v_00_u03b2_2717_, v_f_2718_, v_keys_2719_, v_vals_2720_, v_heq_2721_, v_i_2722_, v_acc_2723_);
lean_dec_ref(v_vals_2720_);
lean_dec_ref(v_keys_2719_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_2725_, lean_object* v_x2_2726_){
_start:
{
lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v___x_2729_; 
v_fst_2727_ = lean_ctor_get(v_x2_2726_, 0);
lean_inc(v_fst_2727_);
v_snd_2728_ = lean_ctor_get(v_x2_2726_, 1);
lean_inc(v_snd_2728_);
lean_dec_ref(v_x2_2726_);
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2727_, v_snd_2728_, v_x1_2725_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_2749_, lean_object* v_x1_2750_, lean_object* v_x2_2751_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_array_get_size(v_x2_2751_);
v___x_2754_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2755_ = lean_nat_dec_lt(v___x_2752_, v___x_2753_);
if (v___x_2755_ == 0)
{
lean_dec_ref(v_x2_2751_);
lean_dec_ref(v___f_2749_);
return v_x1_2750_;
}
else
{
uint8_t v___x_2756_; 
v___x_2756_ = lean_nat_dec_le(v___x_2753_, v___x_2753_);
if (v___x_2756_ == 0)
{
if (v___x_2755_ == 0)
{
lean_dec_ref(v_x2_2751_);
lean_dec_ref(v___f_2749_);
return v_x1_2750_;
}
else
{
size_t v___x_2757_; size_t v___x_2758_; lean_object* v___x_2759_; 
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = lean_usize_of_nat(v___x_2753_);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2754_, v___f_2749_, v_x2_2751_, v___x_2757_, v___x_2758_, v_x1_2750_);
return v___x_2759_;
}
}
else
{
size_t v___x_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = lean_usize_of_nat(v___x_2753_);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2754_, v___f_2749_, v_x2_2751_, v___x_2760_, v___x_2761_, v_x1_2750_);
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_2766_, lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, lean_object* v_toPure_2771_, lean_object* v___f_2772_, lean_object* v_env_2773_){
_start:
{
lean_object* v___x_2774_; lean_object* v_ext_2775_; lean_object* v_toEnvExtension_2776_; lean_object* v_asyncMode_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v_categories_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2774_ = l_Lean_Parser_parserExtension;
v_ext_2775_ = lean_ctor_get(v___x_2774_, 1);
v_toEnvExtension_2776_ = lean_ctor_get(v_ext_2775_, 0);
v_asyncMode_2777_ = lean_ctor_get(v_toEnvExtension_2776_, 2);
v___x_2778_ = 0;
lean_inc_ref(v_env_2773_);
v___x_2779_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2766_, v___x_2774_, v_env_2773_, v_asyncMode_2777_, v___x_2778_);
v_categories_2780_ = lean_ctor_get(v___x_2779_, 2);
lean_inc_ref(v_categories_2780_);
lean_dec(v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2782_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2767_, v___x_2768_, v_categories_2780_, v___x_2781_);
lean_dec_ref(v_categories_2780_);
if (lean_obj_tag(v___x_2782_) == 1)
{
lean_object* v_val_2783_; lean_object* v___y_2785_; lean_object* v___x_2792_; lean_object* v_toEnvExtension_2793_; lean_object* v_exportEntriesFn_2794_; lean_object* v_asyncMode_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v_importedEntries_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v_exported_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v_val_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2792_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2793_ = lean_ctor_get(v___x_2792_, 0);
v_exportEntriesFn_2794_ = lean_ctor_get(v___x_2792_, 4);
v_asyncMode_2795_ = lean_ctor_get(v_toEnvExtension_2793_, 2);
v___x_2796_ = lean_box(0);
lean_inc_ref_n(v_env_2773_, 2);
v___x_2797_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2769_, v_toEnvExtension_2793_, v_env_2773_, v_asyncMode_2795_, v___x_2796_, v___x_2778_);
v_importedEntries_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc_ref(v_importedEntries_2798_);
lean_dec(v___x_2797_);
v___x_2799_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2770_, v___x_2792_, v_env_2773_, v_asyncMode_2795_, v___x_2796_, v___x_2778_);
lean_inc_ref(v_exportEntriesFn_2794_);
v___x_2800_ = lean_apply_2(v_exportEntriesFn_2794_, v_env_2773_, v___x_2799_);
v_exported_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_exported_2801_);
lean_dec_ref(v___x_2800_);
v___x_2802_ = lean_box(1);
v___x_2803_ = lean_array_push(v_importedEntries_2798_, v_exported_2801_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = lean_array_get_size(v___x_2803_);
v___x_2806_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2807_ = lean_nat_dec_lt(v___x_2804_, v___x_2805_);
if (v___x_2807_ == 0)
{
lean_dec_ref(v___x_2803_);
lean_dec_ref(v___f_2772_);
v___y_2785_ = v___x_2802_;
goto v___jp_2784_;
}
else
{
uint8_t v___x_2808_; 
v___x_2808_ = lean_nat_dec_le(v___x_2805_, v___x_2805_);
if (v___x_2808_ == 0)
{
if (v___x_2807_ == 0)
{
lean_dec_ref(v___x_2803_);
lean_dec_ref(v___f_2772_);
v___y_2785_ = v___x_2802_;
goto v___jp_2784_;
}
else
{
size_t v___x_2809_; size_t v___x_2810_; lean_object* v___x_2811_; 
v___x_2809_ = ((size_t)0ULL);
v___x_2810_ = lean_usize_of_nat(v___x_2805_);
v___x_2811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2806_, v___f_2772_, v___x_2803_, v___x_2809_, v___x_2810_, v___x_2802_);
v___y_2785_ = v___x_2811_;
goto v___jp_2784_;
}
}
else
{
size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = ((size_t)0ULL);
v___x_2813_ = lean_usize_of_nat(v___x_2805_);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2806_, v___f_2772_, v___x_2803_, v___x_2812_, v___x_2813_, v___x_2802_);
v___y_2785_ = v___x_2814_;
goto v___jp_2784_;
}
}
v___jp_2784_:
{
lean_object* v_tables_2786_; lean_object* v_leadingTable_2787_; lean_object* v_trailingTable_2788_; lean_object* v_firstTokens_2789_; lean_object* v_firstTokens_2790_; lean_object* v___x_2791_; 
v_tables_2786_ = lean_ctor_get(v_val_2783_, 2);
v_leadingTable_2787_ = lean_ctor_get(v_tables_2786_, 0);
v_trailingTable_2788_ = lean_ctor_get(v_tables_2786_, 2);
lean_inc(v_trailingTable_2788_);
lean_inc(v_leadingTable_2787_);
lean_inc(v_val_2783_);
v_firstTokens_2789_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2783_, v_leadingTable_2787_, v___y_2785_);
v_firstTokens_2790_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2783_, v_trailingTable_2788_, v_firstTokens_2789_);
v___x_2791_ = lean_apply_2(v_toPure_2771_, lean_box(0), v_firstTokens_2790_);
return v___x_2791_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec(v___x_2782_);
lean_dec_ref(v_env_2773_);
lean_dec_ref(v___f_2772_);
lean_dec(v___x_2770_);
v___x_2815_ = lean_box(1);
v___x_2816_ = lean_apply_2(v_toPure_2771_, lean_box(0), v___x_2815_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v_toPure_2822_, lean_object* v___f_2823_, lean_object* v_env_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_2817_, v___x_2818_, v___x_2819_, v___x_2820_, v___x_2821_, v_toPure_2822_, v___f_2823_, v_env_2824_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2817_);
return v_res_2825_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_box(1);
v___x_2830_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_2833_, lean_object* v_inst_2834_){
_start:
{
lean_object* v_toApplicative_2835_; lean_object* v_toBind_2836_; lean_object* v_getEnv_2837_; lean_object* v_toPure_2838_; lean_object* v___f_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; 
v_toApplicative_2835_ = lean_ctor_get(v_inst_2833_, 0);
lean_inc_ref(v_toApplicative_2835_);
v_toBind_2836_ = lean_ctor_get(v_inst_2833_, 1);
lean_inc(v_toBind_2836_);
lean_dec_ref(v_inst_2833_);
v_getEnv_2837_ = lean_ctor_get(v_inst_2834_, 0);
lean_inc(v_getEnv_2837_);
lean_dec_ref(v_inst_2834_);
v_toPure_2838_ = lean_ctor_get(v_toApplicative_2835_, 1);
lean_inc(v_toPure_2838_);
lean_dec_ref(v_toApplicative_2835_);
v___f_2839_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_2840_ = lean_box(1);
v___x_2841_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2842_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2843_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_2844_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2845_, 0, v___x_2844_);
lean_closure_set(v___f_2845_, 1, v___x_2842_);
lean_closure_set(v___f_2845_, 2, v___x_2843_);
lean_closure_set(v___f_2845_, 3, v___x_2841_);
lean_closure_set(v___f_2845_, 4, v___x_2840_);
lean_closure_set(v___f_2845_, 5, v_toPure_2838_);
lean_closure_set(v___f_2845_, 6, v___f_2839_);
v___x_2846_ = lean_apply_4(v_toBind_2836_, lean_box(0), lean_box(0), v_getEnv_2837_, v___f_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_2848_, v_inst_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2853_ = lean_box(1);
v___x_2854_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_2855_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2854_);
lean_ctor_set(v___x_2856_, 2, v___x_2853_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_2858_, lean_object* v___y_2859_, lean_object* v_toPure_2860_, lean_object* v_firsts_2861_, lean_object* v_____do__lift_2862_){
_start:
{
lean_object* v___y_2864_; lean_object* v_val_2875_; 
if (lean_obj_tag(v_____do__lift_2862_) == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_2858_);
v___x_2878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_2877_, v_firsts_2861_, v_n_2858_);
if (lean_obj_tag(v___x_2878_) == 0)
{
uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = 1;
lean_inc(v_n_2858_);
v___x_2880_ = l_Lean_Name_toString(v_n_2858_, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
v___y_2864_ = v___x_2881_;
goto v___jp_2863_;
}
else
{
lean_object* v_val_2882_; 
v_val_2882_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v___x_2878_, 1);
v_val_2875_ = v_val_2882_;
goto v___jp_2874_;
}
}
else
{
lean_object* v_val_2883_; 
lean_dec(v_firsts_2861_);
v_val_2883_ = lean_ctor_get(v_____do__lift_2862_, 0);
lean_inc(v_val_2883_);
lean_dec_ref_known(v_____do__lift_2862_, 1);
v_val_2875_ = v_val_2883_;
goto v___jp_2874_;
}
v___jp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2865_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_2866_ = l_Lean_Expr_const___override(v_n_2858_, v___y_2859_);
v___x_2867_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_2868_ = lean_box(0);
v___x_2869_ = 0;
v___x_2870_ = l_Lean_MessageData_withExprHover(v___y_2864_, v___x_2866_, v___x_2867_, v___x_2868_, v___x_2868_, v___x_2868_, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2865_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2865_);
v___x_2873_ = lean_apply_2(v_toPure_2860_, lean_box(0), v___x_2872_);
return v___x_2873_;
}
v___jp_2874_:
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_val_2875_);
v___y_2864_ = v___x_2876_;
goto v___jp_2863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_2884_, lean_object* v_toPure_2885_, lean_object* v_firsts_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_toBind_2889_, lean_object* v___x_2890_, lean_object* v___x_2891_, lean_object* v___f_2892_, lean_object* v_env_2893_){
_start:
{
lean_object* v___y_2895_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = l_Lean_Environment_constants(v_env_2893_);
lean_inc(v_n_2884_);
v___x_2900_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_2890_, v___x_2891_, v___x_2899_, v_n_2884_);
lean_dec_ref(v___x_2899_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v___x_2901_; 
lean_dec_ref(v___f_2892_);
v___x_2901_ = lean_box(0);
v___y_2895_ = v___x_2901_;
goto v___jp_2894_;
}
else
{
lean_object* v_val_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_val_2902_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2903_ = l_Lean_ConstantInfo_levelParams(v_val_2902_);
lean_dec(v_val_2902_);
v___x_2904_ = lean_box(0);
v___x_2905_ = l_List_mapTR_loop___redArg(v___f_2892_, v___x_2903_, v___x_2904_);
v___y_2895_ = v___x_2905_;
goto v___jp_2894_;
}
v___jp_2894_:
{
lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_inc(v_n_2884_);
v___f_2896_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2896_, 0, v_n_2884_);
lean_closure_set(v___f_2896_, 1, v___y_2895_);
lean_closure_set(v___f_2896_, 2, v_toPure_2885_);
lean_closure_set(v___f_2896_, 3, v_firsts_2886_);
v___x_2897_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_2887_, v_inst_2888_, v_n_2884_);
v___x_2898_ = lean_apply_4(v_toBind_2889_, lean_box(0), lean_box(0), v___x_2897_, v___f_2896_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_firsts_2909_, lean_object* v_n_2910_){
_start:
{
lean_object* v_toApplicative_2911_; lean_object* v_toBind_2912_; lean_object* v_getEnv_2913_; lean_object* v_toPure_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; 
v_toApplicative_2911_ = lean_ctor_get(v_inst_2907_, 0);
v_toBind_2912_ = lean_ctor_get(v_inst_2907_, 1);
lean_inc_n(v_toBind_2912_, 2);
v_getEnv_2913_ = lean_ctor_get(v_inst_2908_, 0);
lean_inc(v_getEnv_2913_);
v_toPure_2914_ = lean_ctor_get(v_toApplicative_2911_, 1);
lean_inc(v_toPure_2914_);
v___f_2915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_2916_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2917_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_2918_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_2918_, 0, v_n_2910_);
lean_closure_set(v___f_2918_, 1, v_toPure_2914_);
lean_closure_set(v___f_2918_, 2, v_firsts_2909_);
lean_closure_set(v___f_2918_, 3, v_inst_2907_);
lean_closure_set(v___f_2918_, 4, v_inst_2908_);
lean_closure_set(v___f_2918_, 5, v_toBind_2912_);
lean_closure_set(v___f_2918_, 6, v___x_2916_);
lean_closure_set(v___f_2918_, 7, v___x_2917_);
lean_closure_set(v___f_2918_, 8, v___f_2915_);
v___x_2919_ = lean_apply_4(v_toBind_2912_, lean_box(0), lean_box(0), v_getEnv_2913_, v___f_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_firsts_2923_, lean_object* v_n_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_2921_, v_inst_2922_, v_firsts_2923_, v_n_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_2931_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_2935_);
lean_dec_ref(v_s_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_2937_, lean_object* v_x1_2938_, lean_object* v_x2_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = l_Lean_Name_toString(v_x1_2938_, v___x_2937_);
v___x_2941_ = l_Lean_Name_toString(v_x2_2939_, v___x_2937_);
v___x_2942_ = lean_string_dec_lt(v___x_2940_, v___x_2941_);
lean_dec_ref(v___x_2941_);
lean_dec_ref(v___x_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_2943_, lean_object* v_x1_2944_, lean_object* v_x2_2945_){
_start:
{
uint8_t v___x_16971__boxed_2946_; uint8_t v_res_2947_; lean_object* v_r_2948_; 
v___x_16971__boxed_2946_ = lean_unbox(v___x_2943_);
v_res_2947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16971__boxed_2946_, v_x1_2944_, v_x2_2945_);
v_r_2948_ = lean_box(v_res_2947_);
return v_r_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_2949_, lean_object* v_pivot_2950_, lean_object* v_as_2951_, lean_object* v_i_2952_, lean_object* v_k_2953_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_nat_dec_lt(v_k_2953_, v_hi_2949_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v_k_2953_);
lean_dec(v_pivot_2950_);
v___x_2955_ = lean_array_fswap(v_as_2951_, v_i_2952_, v_hi_2949_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v_i_2952_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
return v___x_2956_;
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2957_ = lean_array_fget_borrowed(v_as_2951_, v_k_2953_);
lean_inc(v___x_2957_);
v___x_2958_ = l_Lean_Name_toString(v___x_2957_, v___x_2954_);
lean_inc(v_pivot_2950_);
v___x_2959_ = l_Lean_Name_toString(v_pivot_2950_, v___x_2954_);
v___x_2960_ = lean_string_dec_lt(v___x_2958_, v___x_2959_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v___x_2958_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = lean_nat_add(v_k_2953_, v___x_2961_);
lean_dec(v_k_2953_);
v_k_2953_ = v___x_2962_;
goto _start;
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2964_ = lean_array_fswap(v_as_2951_, v_i_2952_, v_k_2953_);
v___x_2965_ = lean_unsigned_to_nat(1u);
v___x_2966_ = lean_nat_add(v_i_2952_, v___x_2965_);
lean_dec(v_i_2952_);
v___x_2967_ = lean_nat_add(v_k_2953_, v___x_2965_);
lean_dec(v_k_2953_);
v_as_2951_ = v___x_2964_;
v_i_2952_ = v___x_2966_;
v_k_2953_ = v___x_2967_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_2969_, lean_object* v_pivot_2970_, lean_object* v_as_2971_, lean_object* v_i_2972_, lean_object* v_k_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2969_, v_pivot_2970_, v_as_2971_, v_i_2972_, v_k_2973_);
lean_dec(v_hi_2969_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_2975_, lean_object* v_as_2976_, lean_object* v_lo_2977_, lean_object* v_hi_2978_){
_start:
{
lean_object* v___y_2980_; uint8_t v___x_2990_; 
v___x_2990_ = lean_nat_dec_lt(v_lo_2977_, v_hi_2978_);
if (v___x_2990_ == 0)
{
lean_dec(v_lo_2977_);
return v_as_2976_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v_mid_2993_; lean_object* v___y_2995_; lean_object* v___y_3001_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_2991_ = lean_nat_add(v_lo_2977_, v_hi_2978_);
v___x_2992_ = lean_unsigned_to_nat(1u);
v_mid_2993_ = lean_nat_shiftr(v___x_2991_, v___x_2992_);
lean_dec(v___x_2991_);
v___x_3006_ = lean_array_fget_borrowed(v_as_2976_, v_mid_2993_);
v___x_3007_ = lean_array_fget_borrowed(v_as_2976_, v_lo_2977_);
lean_inc(v___x_3007_);
lean_inc(v___x_3006_);
v___x_3008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2990_, v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
v___y_3001_ = v_as_2976_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_array_fswap(v_as_2976_, v_lo_2977_, v_mid_2993_);
v___y_3001_ = v___x_3009_;
goto v___jp_3000_;
}
v___jp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = lean_array_fget_borrowed(v___y_2995_, v_mid_2993_);
v___x_2997_ = lean_array_fget_borrowed(v___y_2995_, v_hi_2978_);
lean_inc(v___x_2997_);
lean_inc(v___x_2996_);
v___x_2998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2990_, v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_dec(v_mid_2993_);
v___y_2980_ = v___y_2995_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_array_fswap(v___y_2995_, v_mid_2993_, v_hi_2978_);
lean_dec(v_mid_2993_);
v___y_2980_ = v___x_2999_;
goto v___jp_2979_;
}
}
v___jp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_array_fget_borrowed(v___y_3001_, v_hi_2978_);
v___x_3003_ = lean_array_fget_borrowed(v___y_3001_, v_lo_2977_);
lean_inc(v___x_3003_);
lean_inc(v___x_3002_);
v___x_3004_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2990_, v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
v___y_2995_ = v___y_3001_;
goto v___jp_2994_;
}
else
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_array_fswap(v___y_3001_, v_lo_2977_, v_hi_2978_);
v___y_2995_ = v___x_3005_;
goto v___jp_2994_;
}
}
}
v___jp_2979_:
{
lean_object* v_pivot_2981_; lean_object* v___x_2982_; lean_object* v_fst_2983_; lean_object* v_snd_2984_; uint8_t v___x_2985_; 
v_pivot_2981_ = lean_array_fget(v___y_2980_, v_hi_2978_);
lean_inc_n(v_lo_2977_, 2);
v___x_2982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2978_, v_pivot_2981_, v___y_2980_, v_lo_2977_, v_lo_2977_);
v_fst_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_fst_2983_);
v_snd_2984_ = lean_ctor_get(v___x_2982_, 1);
lean_inc(v_snd_2984_);
lean_dec_ref(v___x_2982_);
v___x_2985_ = lean_nat_dec_le(v_hi_2978_, v_fst_2983_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2975_, v_snd_2984_, v_lo_2977_, v_fst_2983_);
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_nat_add(v_fst_2983_, v___x_2987_);
lean_dec(v_fst_2983_);
v_as_2976_ = v___x_2986_;
v_lo_2977_ = v___x_2988_;
goto _start;
}
else
{
lean_dec(v_fst_2983_);
lean_dec(v_lo_2977_);
return v_snd_2984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_3010_, lean_object* v_as_3011_, lean_object* v_lo_3012_, lean_object* v_hi_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3010_, v_as_3011_, v_lo_3012_, v_hi_3013_);
lean_dec(v_hi_3013_);
lean_dec(v_n_3010_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_3015_, lean_object* v_x_3016_){
_start:
{
if (lean_obj_tag(v_x_3016_) == 0)
{
lean_object* v_k_3017_; lean_object* v_l_3018_; lean_object* v_r_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_k_3017_ = lean_ctor_get(v_x_3016_, 1);
lean_inc(v_k_3017_);
v_l_3018_ = lean_ctor_get(v_x_3016_, 3);
lean_inc(v_l_3018_);
v_r_3019_ = lean_ctor_get(v_x_3016_, 4);
lean_inc(v_r_3019_);
lean_dec_ref_known(v_x_3016_, 5);
v___x_3020_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_3015_, v_l_3018_);
v___x_3021_ = lean_array_push(v___x_3020_, v_k_3017_);
v_init_3015_ = v___x_3021_;
v_x_3016_ = v_r_3019_;
goto _start;
}
else
{
return v_init_3015_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
if (lean_obj_tag(v_a_3023_) == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = l_List_reverse___redArg(v_a_3024_);
return v___x_3025_;
}
else
{
lean_object* v_head_3026_; lean_object* v_tail_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3036_; 
v_head_3026_ = lean_ctor_get(v_a_3023_, 0);
v_tail_3027_ = lean_ctor_get(v_a_3023_, 1);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_a_3023_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3029_ = v_a_3023_;
v_isShared_3030_ = v_isSharedCheck_3036_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_tail_3027_);
lean_inc(v_head_3026_);
lean_dec(v_a_3023_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3036_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3031_ = l_Lean_Level_param___override(v_head_3026_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v_a_3024_);
lean_ctor_set(v___x_3029_, 0, v___x_3031_);
v___x_3033_ = v___x_3029_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_a_3024_);
v___x_3033_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
v_a_3023_ = v_tail_3027_;
v_a_3024_ = v___x_3033_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_3037_, lean_object* v_x2_3038_){
_start:
{
lean_object* v_fst_3039_; lean_object* v_fst_3040_; uint8_t v___x_3041_; 
v_fst_3039_ = lean_ctor_get(v_x1_3037_, 0);
v_fst_3040_ = lean_ctor_get(v_x2_3038_, 0);
v___x_3041_ = l_Lean_Name_quickLt(v_fst_3039_, v_fst_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_3042_, lean_object* v_x2_3043_){
_start:
{
uint8_t v_res_3044_; lean_object* v_r_3045_; 
v_res_3044_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_3042_, v_x2_3043_);
lean_dec_ref(v_x2_3043_);
lean_dec_ref(v_x1_3042_);
v_r_3045_ = lean_box(v_res_3044_);
return v_r_3045_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_3046_, lean_object* v_k_3047_, lean_object* v_x_3048_, lean_object* v_x_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v_m_3052_; lean_object* v_a_3053_; uint8_t v___x_3054_; 
v___x_3050_ = lean_nat_add(v_x_3048_, v_x_3049_);
v___x_3051_ = lean_unsigned_to_nat(1u);
v_m_3052_ = lean_nat_shiftr(v___x_3050_, v___x_3051_);
lean_dec(v___x_3050_);
v_a_3053_ = lean_array_fget_borrowed(v_as_3046_, v_m_3052_);
v___x_3054_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_3053_, v_k_3047_);
if (v___x_3054_ == 0)
{
uint8_t v___x_3055_; 
lean_dec(v_x_3049_);
v___x_3055_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_3047_, v_a_3053_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v_m_3052_);
lean_dec(v_x_3048_);
lean_inc(v_a_3053_);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_a_3053_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_nat_dec_eq(v_m_3052_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = lean_nat_sub(v_m_3052_, v___x_3051_);
lean_dec(v_m_3052_);
v___x_3060_ = lean_nat_dec_lt(v___x_3059_, v_x_3048_);
if (v___x_3060_ == 0)
{
v_x_3049_ = v___x_3059_;
goto _start;
}
else
{
lean_object* v___x_3062_; 
lean_dec(v___x_3059_);
lean_dec(v_x_3048_);
v___x_3062_ = lean_box(0);
return v___x_3062_;
}
}
else
{
lean_object* v___x_3063_; 
lean_dec(v_m_3052_);
lean_dec(v_x_3048_);
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
}
}
else
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
lean_dec(v_x_3048_);
v___x_3064_ = lean_nat_add(v_m_3052_, v___x_3051_);
lean_dec(v_m_3052_);
v___x_3065_ = lean_nat_dec_le(v___x_3064_, v_x_3049_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; 
lean_dec(v___x_3064_);
lean_dec(v_x_3049_);
v___x_3066_ = lean_box(0);
return v___x_3066_;
}
else
{
v_x_3048_ = v___x_3064_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_3068_, lean_object* v_k_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3068_, v_k_3069_, v_x_3070_, v_x_3071_);
lean_dec_ref(v_k_3069_);
lean_dec_ref(v_as_3068_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v_env_3081_; lean_object* v___x_3082_; 
v___x_3076_ = lean_box(1);
v___x_3077_ = lean_st_ref_get(v___y_3074_);
v_env_3081_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3081_);
lean_dec(v___x_3077_);
v___x_3082_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3081_, v_tac_3073_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3083_; lean_object* v_toEnvExtension_3084_; lean_object* v_asyncMode_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3083_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3084_ = lean_ctor_get(v___x_3083_, 0);
v_asyncMode_3085_ = lean_ctor_get(v_toEnvExtension_3084_, 2);
v___x_3086_ = lean_box(0);
v___x_3087_ = 0;
v___x_3088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3076_, v___x_3083_, v_env_3081_, v_asyncMode_3085_, v___x_3086_, v___x_3087_);
v___x_3089_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3088_, v_tac_3073_);
lean_dec(v_tac_3073_);
lean_dec(v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
else
{
lean_object* v_val_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3119_; 
v_val_3091_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3093_ = v___x_3082_;
v_isShared_3094_ = v_isSharedCheck_3119_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_val_3091_);
lean_dec(v___x_3082_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3119_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; uint8_t v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3095_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3096_ = 0;
v___x_3097_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3076_, v___x_3095_, v_env_3081_, v_val_3091_, v___x_3096_);
lean_dec(v_val_3091_);
lean_dec_ref(v_env_3081_);
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = lean_array_get_size(v___x_3097_);
v___x_3100_ = lean_nat_dec_lt(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_dec_ref(v___x_3097_);
lean_del_object(v___x_3093_);
lean_dec(v_tac_3073_);
goto v___jp_3078_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_sub(v___x_3099_, v___x_3101_);
v___x_3103_ = lean_nat_dec_le(v___x_3098_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_dec(v___x_3102_);
lean_dec_ref(v___x_3097_);
lean_del_object(v___x_3093_);
lean_dec(v_tac_3073_);
goto v___jp_3078_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v_tac_3073_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_3097_, v___x_3105_, v___x_3098_, v___x_3102_);
lean_dec_ref_known(v___x_3105_, 2);
lean_dec_ref(v___x_3097_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_del_object(v___x_3093_);
goto v___jp_3078_;
}
else
{
lean_object* v_val_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3118_; 
v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_val_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_snd_3111_; lean_object* v___x_3113_; 
v_snd_3111_ = lean_ctor_get(v_val_3107_, 1);
lean_inc(v_snd_3111_);
lean_dec(v_val_3107_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v_snd_3111_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_snd_3111_);
v___x_3113_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3115_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set_tag(v___x_3093_, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3113_);
v___x_3115_ = v___x_3093_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
}
}
v___jp_3078_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3120_, v___y_3121_);
lean_dec(v___y_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_3124_, lean_object* v_k_3125_){
_start:
{
if (lean_obj_tag(v_t_3124_) == 0)
{
lean_object* v_k_3126_; lean_object* v_v_3127_; lean_object* v_l_3128_; lean_object* v_r_3129_; uint8_t v___x_3130_; 
v_k_3126_ = lean_ctor_get(v_t_3124_, 1);
v_v_3127_ = lean_ctor_get(v_t_3124_, 2);
v_l_3128_ = lean_ctor_get(v_t_3124_, 3);
v_r_3129_ = lean_ctor_get(v_t_3124_, 4);
v___x_3130_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3125_, v_k_3126_);
switch(v___x_3130_)
{
case 0:
{
v_t_3124_ = v_l_3128_;
goto _start;
}
case 1:
{
lean_object* v___x_3132_; 
lean_inc(v_v_3127_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_v_3127_);
return v___x_3132_;
}
default: 
{
v_t_3124_ = v_r_3129_;
goto _start;
}
}
}
else
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_box(0);
return v___x_3134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_3135_, lean_object* v_k_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3135_, v_k_3136_);
lean_dec(v_k_3136_);
lean_dec(v_t_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_3138_, lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_box(0);
return v___x_3140_;
}
else
{
lean_object* v_key_3141_; lean_object* v_value_3142_; lean_object* v_tail_3143_; uint8_t v___x_3144_; 
v_key_3141_ = lean_ctor_get(v_x_3139_, 0);
v_value_3142_ = lean_ctor_get(v_x_3139_, 1);
v_tail_3143_ = lean_ctor_get(v_x_3139_, 2);
v___x_3144_ = lean_name_eq(v_key_3141_, v_a_3138_);
if (v___x_3144_ == 0)
{
v_x_3139_ = v_tail_3143_;
goto _start;
}
else
{
lean_object* v___x_3146_; 
lean_inc(v_value_3142_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v_value_3142_);
return v___x_3146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_3147_, lean_object* v_x_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3147_, v_x_3148_);
lean_dec(v_x_3148_);
lean_dec(v_a_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_buckets_3152_; lean_object* v___x_3153_; uint64_t v___y_3155_; 
v_buckets_3152_ = lean_ctor_get(v_m_3150_, 1);
v___x_3153_ = lean_array_get_size(v_buckets_3152_);
if (lean_obj_tag(v_a_3151_) == 0)
{
uint64_t v___x_3169_; 
v___x_3169_ = 1723ULL;
v___y_3155_ = v___x_3169_;
goto v___jp_3154_;
}
else
{
uint64_t v_hash_3170_; 
v_hash_3170_ = lean_ctor_get_uint64(v_a_3151_, sizeof(void*)*2);
v___y_3155_ = v_hash_3170_;
goto v___jp_3154_;
}
v___jp_3154_:
{
uint64_t v___x_3156_; uint64_t v___x_3157_; uint64_t v_fold_3158_; uint64_t v___x_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; size_t v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3156_ = 32ULL;
v___x_3157_ = lean_uint64_shift_right(v___y_3155_, v___x_3156_);
v_fold_3158_ = lean_uint64_xor(v___y_3155_, v___x_3157_);
v___x_3159_ = 16ULL;
v___x_3160_ = lean_uint64_shift_right(v_fold_3158_, v___x_3159_);
v___x_3161_ = lean_uint64_xor(v_fold_3158_, v___x_3160_);
v___x_3162_ = lean_uint64_to_usize(v___x_3161_);
v___x_3163_ = lean_usize_of_nat(v___x_3153_);
v___x_3164_ = ((size_t)1ULL);
v___x_3165_ = lean_usize_sub(v___x_3163_, v___x_3164_);
v___x_3166_ = lean_usize_land(v___x_3162_, v___x_3165_);
v___x_3167_ = lean_array_uget_borrowed(v_buckets_3152_, v___x_3166_);
v___x_3168_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3151_, v___x_3167_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3171_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec_ref(v_m_3171_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_3174_, lean_object* v_vals_3175_, lean_object* v_i_3176_, lean_object* v_k_3177_){
_start:
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = lean_array_get_size(v_keys_3174_);
v___x_3179_ = lean_nat_dec_lt(v_i_3176_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; 
lean_dec(v_i_3176_);
v___x_3180_ = lean_box(0);
return v___x_3180_;
}
else
{
lean_object* v_k_x27_3181_; uint8_t v___x_3182_; 
v_k_x27_3181_ = lean_array_fget_borrowed(v_keys_3174_, v_i_3176_);
v___x_3182_ = lean_name_eq(v_k_3177_, v_k_x27_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_unsigned_to_nat(1u);
v___x_3184_ = lean_nat_add(v_i_3176_, v___x_3183_);
lean_dec(v_i_3176_);
v_i_3176_ = v___x_3184_;
goto _start;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_array_fget_borrowed(v_vals_3175_, v_i_3176_);
lean_dec(v_i_3176_);
lean_inc(v___x_3186_);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_3188_, lean_object* v_vals_3189_, lean_object* v_i_3190_, lean_object* v_k_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3188_, v_vals_3189_, v_i_3190_, v_k_3191_);
lean_dec(v_k_3191_);
lean_dec_ref(v_vals_3189_);
lean_dec_ref(v_keys_3188_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3193_, size_t v_x_3194_, lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3193_) == 0)
{
lean_object* v_es_3196_; lean_object* v___x_3197_; size_t v___x_3198_; size_t v___x_3199_; lean_object* v_j_3200_; lean_object* v___x_3201_; 
v_es_3196_ = lean_ctor_get(v_x_3193_, 0);
v___x_3197_ = lean_box(2);
v___x_3198_ = ((size_t)31ULL);
v___x_3199_ = lean_usize_land(v_x_3194_, v___x_3198_);
v_j_3200_ = lean_usize_to_nat(v___x_3199_);
v___x_3201_ = lean_array_get_borrowed(v___x_3197_, v_es_3196_, v_j_3200_);
lean_dec(v_j_3200_);
switch(lean_obj_tag(v___x_3201_))
{
case 0:
{
lean_object* v_key_3202_; lean_object* v_val_3203_; uint8_t v___x_3204_; 
v_key_3202_ = lean_ctor_get(v___x_3201_, 0);
v_val_3203_ = lean_ctor_get(v___x_3201_, 1);
v___x_3204_ = lean_name_eq(v_x_3195_, v_key_3202_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_box(0);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; 
lean_inc(v_val_3203_);
v___x_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_val_3203_);
return v___x_3206_;
}
}
case 1:
{
lean_object* v_node_3207_; size_t v___x_3208_; size_t v___x_3209_; 
v_node_3207_ = lean_ctor_get(v___x_3201_, 0);
v___x_3208_ = ((size_t)5ULL);
v___x_3209_ = lean_usize_shift_right(v_x_3194_, v___x_3208_);
v_x_3193_ = v_node_3207_;
v_x_3194_ = v___x_3209_;
goto _start;
}
default: 
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_box(0);
return v___x_3211_;
}
}
}
else
{
lean_object* v_ks_3212_; lean_object* v_vs_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v_ks_3212_ = lean_ctor_get(v_x_3193_, 0);
v_vs_3213_ = lean_ctor_get(v_x_3193_, 1);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_3212_, v_vs_3213_, v___x_3214_, v_x_3195_);
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
size_t v_x_17344__boxed_3219_; lean_object* v_res_3220_; 
v_x_17344__boxed_3219_ = lean_unbox_usize(v_x_3217_);
lean_dec(v_x_3217_);
v_res_3220_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3216_, v_x_17344__boxed_3219_, v_x_3218_);
lean_dec(v_x_3218_);
lean_dec_ref(v_x_3216_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
uint64_t v___y_3224_; 
if (lean_obj_tag(v_x_3222_) == 0)
{
uint64_t v___x_3227_; 
v___x_3227_ = 1723ULL;
v___y_3224_ = v___x_3227_;
goto v___jp_3223_;
}
else
{
uint64_t v_hash_3228_; 
v_hash_3228_ = lean_ctor_get_uint64(v_x_3222_, sizeof(void*)*2);
v___y_3224_ = v_hash_3228_;
goto v___jp_3223_;
}
v___jp_3223_:
{
size_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_uint64_to_usize(v___y_3224_);
v___x_3226_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3221_, v___x_3225_, v_x_3222_);
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3229_, v_x_3230_);
lean_dec(v_x_3230_);
lean_dec_ref(v_x_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
uint8_t v_stage_u2081_3234_; 
v_stage_u2081_3234_ = lean_ctor_get_uint8(v_x_3232_, sizeof(void*)*2);
if (v_stage_u2081_3234_ == 0)
{
lean_object* v_map_u2081_3235_; lean_object* v_map_u2082_3236_; lean_object* v___x_3237_; 
v_map_u2081_3235_ = lean_ctor_get(v_x_3232_, 0);
v_map_u2082_3236_ = lean_ctor_get(v_x_3232_, 1);
v___x_3237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3235_, v_x_3233_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_3236_, v_x_3233_);
return v___x_3238_;
}
else
{
return v___x_3237_;
}
}
else
{
lean_object* v_map_u2081_3239_; lean_object* v___x_3240_; 
v_map_u2081_3239_ = lean_ctor_get(v_x_3232_, 0);
v___x_3240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3239_, v_x_3233_);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3241_, v_x_3242_);
lean_dec(v_x_3242_);
lean_dec_ref(v_x_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_3244_, lean_object* v_n_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3264_; lean_object* v_val_3265_; lean_object* v___x_3267_; lean_object* v___y_3269_; lean_object* v_env_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3267_ = lean_st_ref_get(v___y_3247_);
v_env_3284_ = lean_ctor_get(v___x_3267_, 0);
lean_inc_ref(v_env_3284_);
lean_dec(v___x_3267_);
v___x_3285_ = l_Lean_Environment_constants(v_env_3284_);
v___x_3286_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_3285_, v_n_3245_);
lean_dec_ref(v___x_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_box(0);
v___y_3269_ = v___x_3287_;
goto v___jp_3268_;
}
else
{
lean_object* v_val_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_val_3288_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_val_3288_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3289_ = l_Lean_ConstantInfo_levelParams(v_val_3288_);
lean_dec(v_val_3288_);
v___x_3290_ = lean_box(0);
v___x_3291_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_3289_, v___x_3290_);
v___y_3269_ = v___x_3291_;
goto v___jp_3268_;
}
v___jp_3249_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3252_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_3253_ = l_Lean_Expr_const___override(v_n_3245_, v___y_3250_);
v___x_3254_ = lean_unsigned_to_nat(32u);
v___x_3255_ = lean_mk_empty_array_with_capacity(v___x_3254_);
lean_dec_ref(v___x_3255_);
v___x_3256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3257_ = lean_box(0);
v___x_3258_ = 0;
v___x_3259_ = l_Lean_MessageData_withExprHover(v___y_3251_, v___x_3253_, v___x_3256_, v___x_3257_, v___x_3257_, v___x_3257_, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3252_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v___x_3252_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
v___jp_3263_:
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_val_3265_);
v___y_3250_ = v___y_3264_;
v___y_3251_ = v___x_3266_;
goto v___jp_3249_;
}
v___jp_3268_:
{
lean_object* v___x_3270_; lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3283_; 
lean_inc(v_n_3245_);
v___x_3270_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_3245_, v___y_3247_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3283_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3283_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
if (lean_obj_tag(v_a_3271_) == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_3244_, v_n_3245_);
if (lean_obj_tag(v___x_3275_) == 0)
{
uint8_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3276_ = 1;
lean_inc(v_n_3245_);
v___x_3277_ = l_Lean_Name_toString(v_n_3245_, v___x_3276_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set_tag(v___x_3273_, 3);
lean_ctor_set(v___x_3273_, 0, v___x_3277_);
v___x_3279_ = v___x_3273_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v___y_3250_ = v___y_3269_;
v___y_3251_ = v___x_3279_;
goto v___jp_3249_;
}
}
else
{
lean_object* v_val_3281_; 
lean_del_object(v___x_3273_);
v_val_3281_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_val_3281_);
lean_dec_ref_known(v___x_3275_, 1);
v___y_3264_ = v___y_3269_;
v_val_3265_ = v_val_3281_;
goto v___jp_3263_;
}
}
else
{
lean_object* v_val_3282_; 
lean_del_object(v___x_3273_);
v_val_3282_ = lean_ctor_get(v_a_3271_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v_a_3271_, 1);
v___y_3264_ = v___y_3269_;
v_val_3265_ = v_val_3282_;
goto v___jp_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_3292_, lean_object* v_n_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3292_, v_n_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v_firsts_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
if (lean_obj_tag(v_x_3299_) == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = l_List_reverse___redArg(v_x_3300_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
else
{
lean_object* v_head_3306_; lean_object* v_tail_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3325_; 
v_head_3306_ = lean_ctor_get(v_x_3299_, 0);
v_tail_3307_ = lean_ctor_get(v_x_3299_, 1);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_x_3299_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3309_ = v_x_3299_;
v_isShared_3310_ = v_isSharedCheck_3325_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_tail_3307_);
lean_inc(v_head_3306_);
lean_dec(v_x_3299_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3325_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_3298_, v_head_3306_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v_x_3300_);
lean_ctor_set(v___x_3309_, 0, v_a_3312_);
v___x_3314_ = v___x_3309_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_x_3300_);
v___x_3314_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
v_x_3299_ = v_tail_3307_;
v_x_3300_ = v___x_3314_;
goto _start;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_del_object(v___x_3309_);
lean_dec(v_tail_3307_);
lean_dec(v_x_3300_);
v_a_3317_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3311_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3311_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3326_, v_x_3327_, v_x_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v_a_3326_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_3333_, lean_object* v___x_3334_, lean_object* v___x_3335_, lean_object* v_a_3336_, lean_object* v_b_3337_){
_start:
{
lean_object* v_it_3339_; lean_object* v_startInclusive_3340_; lean_object* v_endExclusive_3341_; 
if (lean_obj_tag(v_a_3336_) == 0)
{
lean_object* v_currPos_3346_; lean_object* v_searcher_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3370_; 
v_currPos_3346_ = lean_ctor_get(v_a_3336_, 0);
v_searcher_3347_ = lean_ctor_get(v_a_3336_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_a_3336_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3349_ = v_a_3336_;
v_isShared_3350_ = v_isSharedCheck_3370_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_searcher_3347_);
lean_inc(v_currPos_3346_);
lean_dec(v_a_3336_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3370_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
uint8_t v_decide_3351_; 
v_decide_3351_ = lean_nat_dec_eq(v_searcher_3347_, v___x_3335_);
if (v_decide_3351_ == 0)
{
uint32_t v___x_3352_; uint32_t v___x_3353_; uint8_t v___x_3354_; 
v___x_3352_ = 10;
v___x_3353_ = lean_string_utf8_get_fast(v_val_3333_, v_searcher_3347_);
v___x_3354_ = lean_uint32_dec_eq(v___x_3353_, v___x_3352_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = lean_string_utf8_next_fast(v_val_3333_, v_searcher_3347_);
lean_dec(v_searcher_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v___x_3355_);
v___x_3357_ = v___x_3349_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_currPos_3346_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
v_a_3336_ = v___x_3357_;
goto _start;
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v_slice_3363_; lean_object* v_nextIt_3365_; 
v___x_3360_ = lean_string_utf8_next_fast(v_val_3333_, v_searcher_3347_);
v___x_3361_ = lean_nat_sub(v___x_3360_, v_searcher_3347_);
v___x_3362_ = lean_nat_add(v_searcher_3347_, v___x_3361_);
lean_dec(v___x_3361_);
v_slice_3363_ = l_String_Slice_subslice_x21(v___x_3334_, v_currPos_3346_, v_searcher_3347_);
lean_inc(v___x_3362_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v___x_3362_);
lean_ctor_set(v___x_3349_, 0, v___x_3362_);
v_nextIt_3365_ = v___x_3349_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3362_);
v_nextIt_3365_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v_startInclusive_3366_; lean_object* v_endExclusive_3367_; 
v_startInclusive_3366_ = lean_ctor_get(v_slice_3363_, 0);
lean_inc(v_startInclusive_3366_);
v_endExclusive_3367_ = lean_ctor_get(v_slice_3363_, 1);
lean_inc(v_endExclusive_3367_);
lean_dec_ref(v_slice_3363_);
v_it_3339_ = v_nextIt_3365_;
v_startInclusive_3340_ = v_startInclusive_3366_;
v_endExclusive_3341_ = v_endExclusive_3367_;
goto v___jp_3338_;
}
}
}
else
{
lean_object* v___x_3369_; 
lean_del_object(v___x_3349_);
lean_dec(v_searcher_3347_);
v___x_3369_ = lean_box(1);
lean_inc(v___x_3335_);
v_it_3339_ = v___x_3369_;
v_startInclusive_3340_ = v_currPos_3346_;
v_endExclusive_3341_ = v___x_3335_;
goto v___jp_3338_;
}
}
}
else
{
lean_dec(v___x_3335_);
return v_b_3337_;
}
v___jp_3338_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_string_utf8_extract_fast(v_val_3333_, v_startInclusive_3340_, v_endExclusive_3341_);
lean_dec(v_endExclusive_3341_);
lean_dec(v_startInclusive_3340_);
v___x_3343_ = l_Lean_stringToMessageData(v___x_3342_);
v___x_3344_ = lean_array_push(v_b_3337_, v___x_3343_);
v_a_3336_ = v_it_3339_;
v_b_3337_ = v___x_3344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_3371_, lean_object* v___x_3372_, lean_object* v___x_3373_, lean_object* v_a_3374_, lean_object* v_b_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3371_, v___x_3372_, v___x_3373_, v_a_3374_, v_b_3375_);
lean_dec_ref(v___x_3372_);
lean_dec_ref(v_val_3371_);
return v_res_3376_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_3381_ = l_Lean_stringToMessageData(v___x_3380_);
return v___x_3381_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_3384_ = l_Lean_stringToMessageData(v___x_3383_);
return v___x_3384_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_3392_ = l_Lean_MessageData_ofFormat(v___x_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_x_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
if (lean_obj_tag(v_x_3395_) == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = l_List_reverse___redArg(v_x_3396_);
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v_head_3402_; lean_object* v_tail_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3500_; 
v_head_3402_ = lean_ctor_get(v_x_3395_, 0);
v_tail_3403_ = lean_ctor_get(v_x_3395_, 1);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_x_3395_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3405_ = v_x_3395_;
v_isShared_3406_ = v_isSharedCheck_3500_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_tail_3403_);
lean_inc(v_head_3402_);
lean_dec(v_x_3395_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3500_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v_snd_3420_; lean_object* v_fst_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3499_; 
v_snd_3420_ = lean_ctor_get(v_head_3402_, 1);
v_fst_3421_ = lean_ctor_get(v_head_3402_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_head_3402_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3423_ = v_head_3402_;
v_isShared_3424_ = v_isSharedCheck_3499_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snd_3420_);
lean_inc(v_fst_3421_);
lean_dec(v_head_3402_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3499_;
goto v_resetjp_3422_;
}
v___jp_3407_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___y_3409_);
lean_ctor_set(v___x_3412_, 1, v___y_3411_);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___y_3410_);
v___x_3414_ = l_Lean_MessageData_nestD(v___x_3413_);
lean_inc_ref(v___y_3408_);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___y_3408_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v_x_3396_);
lean_ctor_set(v___x_3405_, 0, v___x_3415_);
v___x_3417_ = v___x_3405_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_x_3396_);
v___x_3417_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
v_x_3395_ = v_tail_3403_;
v_x_3396_ = v___x_3417_;
goto _start;
}
}
v_resetjp_3422_:
{
lean_object* v_fst_3425_; lean_object* v_snd_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3498_; 
v_fst_3425_ = lean_ctor_get(v_snd_3420_, 0);
v_snd_3426_ = lean_ctor_get(v_snd_3420_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_snd_3420_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3428_ = v_snd_3420_;
v_isShared_3429_ = v_isSharedCheck_3498_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_snd_3426_);
lean_inc(v_fst_3425_);
lean_dec(v_snd_3420_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3498_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v_a_3453_; lean_object* v___y_3469_; lean_object* v___x_3478_; 
v___x_3478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3394_, v_fst_3421_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_MessageData_nil;
v_a_3453_ = v___x_3479_;
goto v___jp_3452_;
}
else
{
lean_object* v_val_3480_; 
v_val_3480_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v___x_3478_, 1);
if (lean_obj_tag(v_val_3480_) == 0)
{
lean_object* v_size_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_size_3481_ = lean_ctor_get(v_val_3480_, 0);
v___x_3482_ = lean_mk_empty_array_with_capacity(v_size_3481_);
v___x_3483_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_3482_, v_val_3480_);
v___x_3484_ = lean_array_get_size(v___x_3483_);
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = lean_nat_dec_eq(v___x_3484_, v___x_3489_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___y_3494_; uint8_t v___x_3496_; 
v___x_3491_ = lean_unsigned_to_nat(1u);
v___x_3492_ = lean_nat_sub(v___x_3484_, v___x_3491_);
v___x_3496_ = lean_nat_dec_le(v___x_3489_, v___x_3492_);
if (v___x_3496_ == 0)
{
lean_inc(v___x_3492_);
v___y_3494_ = v___x_3492_;
goto v___jp_3493_;
}
else
{
v___y_3494_ = v___x_3489_;
goto v___jp_3493_;
}
v___jp_3493_:
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_nat_dec_le(v___y_3494_, v___x_3492_);
if (v___x_3495_ == 0)
{
lean_dec(v___x_3492_);
lean_inc(v___y_3494_);
v___y_3486_ = v___y_3494_;
v___y_3487_ = v___y_3494_;
goto v___jp_3485_;
}
else
{
v___y_3486_ = v___y_3494_;
v___y_3487_ = v___x_3492_;
goto v___jp_3485_;
}
}
}
else
{
v___y_3469_ = v___x_3483_;
goto v___jp_3468_;
}
v___jp_3485_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_3484_, v___x_3483_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
v___y_3469_ = v___x_3488_;
goto v___jp_3468_;
}
}
else
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_MessageData_nil;
v_a_3453_ = v___x_3497_;
goto v___jp_3452_;
}
}
v___jp_3430_:
{
lean_object* v___x_3436_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set_tag(v___x_3428_, 7);
lean_ctor_set(v___x_3428_, 1, v___y_3434_);
lean_ctor_set(v___x_3428_, 0, v___y_3432_);
v___x_3436_ = v___x_3428_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___y_3432_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___y_3434_);
v___x_3436_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
if (lean_obj_tag(v_snd_3426_) == 0)
{
lean_object* v___x_3437_; 
lean_del_object(v___x_3423_);
v___x_3437_ = l_Lean_MessageData_nil;
v___y_3408_ = v___y_3431_;
v___y_3409_ = v___x_3436_;
v___y_3410_ = v___y_3433_;
v___y_3411_ = v___x_3437_;
goto v___jp_3407_;
}
else
{
lean_object* v_val_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
v_val_3438_ = lean_ctor_get(v_snd_3426_, 0);
lean_inc_n(v_val_3438_, 2);
lean_dec_ref_known(v_snd_3426_, 1);
v___x_3439_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3440_ = lean_unsigned_to_nat(0u);
v___x_3441_ = lean_string_utf8_byte_size(v_val_3438_);
v___x_3442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3442_, 0, v_val_3438_);
lean_ctor_set(v___x_3442_, 1, v___x_3440_);
lean_ctor_set(v___x_3442_, 2, v___x_3441_);
v___x_3443_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_3444_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_3445_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3438_, v___x_3442_, v___x_3441_, v___x_3443_, v___x_3444_);
lean_dec_ref_known(v___x_3442_, 3);
lean_dec(v_val_3438_);
v___x_3446_ = lean_array_to_list(v___x_3445_);
v___x_3447_ = l_Lean_MessageData_joinSep(v___x_3446_, v___x_3439_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 7);
lean_ctor_set(v___x_3423_, 1, v___x_3447_);
lean_ctor_set(v___x_3423_, 0, v___x_3439_);
v___x_3449_ = v___x_3423_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v___y_3408_ = v___y_3431_;
v___y_3409_ = v___x_3436_;
v___y_3410_ = v___y_3433_;
v___y_3411_ = v___x_3449_;
goto v___jp_3407_;
}
}
}
}
v___jp_3452_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3454_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_3455_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
lean_inc(v_fst_3421_);
v___x_3456_ = l_Lean_MessageData_ofName(v_fst_3421_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v___x_3455_);
v___x_3459_ = 1;
v___x_3460_ = l_Lean_Name_toString(v_fst_3421_, v___x_3459_);
v___x_3461_ = lean_string_dec_eq(v___x_3460_, v_fst_3425_);
lean_dec_ref(v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3462_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_3463_ = l_Lean_stringToMessageData(v_fst_3425_);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___y_3431_ = v___x_3454_;
v___y_3432_ = v___x_3458_;
v___y_3433_ = v_a_3453_;
v___y_3434_ = v___x_3466_;
goto v___jp_3430_;
}
else
{
lean_object* v___x_3467_; 
lean_dec(v_fst_3425_);
v___x_3467_ = l_Lean_MessageData_nil;
v___y_3431_ = v___x_3454_;
v___y_3432_ = v___x_3458_;
v___y_3433_ = v_a_3453_;
v___y_3434_ = v___x_3467_;
goto v___jp_3430_;
}
}
v___jp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = lean_array_to_list(v___y_3469_);
v___x_3471_ = lean_box(0);
v___x_3472_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3393_, v___x_3470_, v___x_3471_, v___y_3397_, v___y_3398_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v___x_3474_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3475_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_3476_ = l_Lean_MessageData_joinSep(v_a_3473_, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3474_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v_a_3453_ = v___x_3477_;
goto v___jp_3452_;
}
else
{
lean_del_object(v___x_3428_);
lean_dec(v_snd_3426_);
lean_dec(v_fst_3425_);
lean_del_object(v___x_3423_);
lean_dec(v_fst_3421_);
lean_del_object(v___x_3405_);
lean_dec(v_tail_3403_);
lean_dec(v_x_3396_);
return v___x_3472_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_x_3503_, lean_object* v_x_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3501_, v_a_3502_, v_x_3503_, v_x_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v_a_3502_);
lean_dec(v_a_3501_);
return v_res_3508_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_3510_, uint8_t v___y_3511_, lean_object* v_x_3512_){
_start:
{
if (lean_obj_tag(v_x_3512_) == 1)
{
lean_object* v_pre_3513_; 
v_pre_3513_ = lean_ctor_get(v_x_3512_, 0);
if (lean_obj_tag(v_pre_3513_) == 0)
{
lean_object* v_str_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_str_3514_ = lean_ctor_get(v_x_3512_, 1);
v___x_3515_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_3516_ = lean_string_dec_eq(v_str_3514_, v___x_3515_);
if (v___x_3516_ == 0)
{
return v___x_3516_;
}
else
{
return v_suppressElabErrors_3510_;
}
}
else
{
return v___y_3511_;
}
}
else
{
return v___y_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_3517_, lean_object* v___y_3518_, lean_object* v_x_3519_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3520_; uint8_t v___y_17960__boxed_3521_; uint8_t v_res_3522_; lean_object* v_r_3523_; 
v_suppressElabErrors_boxed_3520_ = lean_unbox(v_suppressElabErrors_3517_);
v___y_17960__boxed_3521_ = lean_unbox(v___y_3518_);
v_res_3522_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_3520_, v___y_17960__boxed_3521_, v_x_3519_);
lean_dec(v_x_3519_);
v_r_3523_ = lean_box(v_res_3522_);
return v_r_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_3524_, lean_object* v_msgData_3525_, uint8_t v_severity_3526_, uint8_t v_isSilent_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___y_3532_; uint8_t v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; uint8_t v___y_3597_; uint8_t v___y_3598_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; uint8_t v___y_3625_; lean_object* v___y_3626_; uint8_t v___y_3627_; uint8_t v___y_3628_; lean_object* v___y_3629_; uint8_t v___y_3633_; uint8_t v___y_3634_; uint8_t v___y_3635_; uint8_t v___x_3650_; uint8_t v___y_3652_; uint8_t v___y_3653_; uint8_t v___y_3654_; uint8_t v___y_3656_; uint8_t v___x_3668_; 
v___x_3650_ = 2;
v___x_3668_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3526_, v___x_3650_);
if (v___x_3668_ == 0)
{
v___y_3656_ = v___x_3668_;
goto v___jp_3655_;
}
else
{
uint8_t v___x_3669_; 
lean_inc_ref(v_msgData_3525_);
v___x_3669_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3525_);
v___y_3656_ = v___x_3669_;
goto v___jp_3655_;
}
v___jp_3531_:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Elab_Command_getScope___redArg(v___y_3539_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v_currNamespace_3542_; lean_object* v___x_3543_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v_currNamespace_3542_ = lean_ctor_get(v_a_3541_, 2);
lean_inc(v_currNamespace_3542_);
lean_dec(v_a_3541_);
v___x_3543_ = l_Lean_Elab_Command_getScope___redArg(v___y_3539_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3579_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3579_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3579_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v_openDecls_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v_env_3553_; lean_object* v_messages_3554_; lean_object* v_scopes_3555_; lean_object* v_usedQuotCtxts_3556_; lean_object* v_nextMacroScope_3557_; lean_object* v_maxRecDepth_3558_; lean_object* v_ngen_3559_; lean_object* v_auxDeclNGen_3560_; lean_object* v_infoState_3561_; lean_object* v_traceState_3562_; lean_object* v_snapshotTasks_3563_; lean_object* v_prevLinterStates_3564_; lean_object* v_codeQualityEntryTasks_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3578_; 
v_openDecls_3548_ = lean_ctor_get(v_a_3544_, 3);
lean_inc(v_openDecls_3548_);
lean_dec(v_a_3544_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_currNamespace_3542_);
lean_ctor_set(v___x_3549_, 1, v_openDecls_3548_);
v___x_3550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v___y_3536_);
lean_inc_ref(v___y_3532_);
lean_inc_ref(v___y_3535_);
v___x_3551_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3551_, 0, v___y_3535_);
lean_ctor_set(v___x_3551_, 1, v___y_3538_);
lean_ctor_set(v___x_3551_, 2, v___y_3537_);
lean_ctor_set(v___x_3551_, 3, v___y_3532_);
lean_ctor_set(v___x_3551_, 4, v___x_3550_);
lean_ctor_set_uint8(v___x_3551_, sizeof(void*)*5, v___y_3534_);
lean_ctor_set_uint8(v___x_3551_, sizeof(void*)*5 + 1, v___y_3533_);
lean_ctor_set_uint8(v___x_3551_, sizeof(void*)*5 + 2, v_isSilent_3527_);
v___x_3552_ = lean_st_ref_take(v___y_3539_);
v_env_3553_ = lean_ctor_get(v___x_3552_, 0);
v_messages_3554_ = lean_ctor_get(v___x_3552_, 1);
v_scopes_3555_ = lean_ctor_get(v___x_3552_, 2);
v_usedQuotCtxts_3556_ = lean_ctor_get(v___x_3552_, 3);
v_nextMacroScope_3557_ = lean_ctor_get(v___x_3552_, 4);
v_maxRecDepth_3558_ = lean_ctor_get(v___x_3552_, 5);
v_ngen_3559_ = lean_ctor_get(v___x_3552_, 6);
v_auxDeclNGen_3560_ = lean_ctor_get(v___x_3552_, 7);
v_infoState_3561_ = lean_ctor_get(v___x_3552_, 8);
v_traceState_3562_ = lean_ctor_get(v___x_3552_, 9);
v_snapshotTasks_3563_ = lean_ctor_get(v___x_3552_, 10);
v_prevLinterStates_3564_ = lean_ctor_get(v___x_3552_, 11);
v_codeQualityEntryTasks_3565_ = lean_ctor_get(v___x_3552_, 12);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3567_ = v___x_3552_;
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3565_);
lean_inc(v_prevLinterStates_3564_);
lean_inc(v_snapshotTasks_3563_);
lean_inc(v_traceState_3562_);
lean_inc(v_infoState_3561_);
lean_inc(v_auxDeclNGen_3560_);
lean_inc(v_ngen_3559_);
lean_inc(v_maxRecDepth_3558_);
lean_inc(v_nextMacroScope_3557_);
lean_inc(v_usedQuotCtxts_3556_);
lean_inc(v_scopes_3555_);
lean_inc(v_messages_3554_);
lean_inc(v_env_3553_);
lean_dec(v___x_3552_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = lean_box(0);
v___x_3570_ = l_Lean_MessageLog_add(v___x_3551_, v_messages_3554_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_env_3553_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_scopes_3555_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_usedQuotCtxts_3556_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_nextMacroScope_3557_);
lean_ctor_set(v_reuseFailAlloc_3577_, 5, v_maxRecDepth_3558_);
lean_ctor_set(v_reuseFailAlloc_3577_, 6, v_ngen_3559_);
lean_ctor_set(v_reuseFailAlloc_3577_, 7, v_auxDeclNGen_3560_);
lean_ctor_set(v_reuseFailAlloc_3577_, 8, v_infoState_3561_);
lean_ctor_set(v_reuseFailAlloc_3577_, 9, v_traceState_3562_);
lean_ctor_set(v_reuseFailAlloc_3577_, 10, v_snapshotTasks_3563_);
lean_ctor_set(v_reuseFailAlloc_3577_, 11, v_prevLinterStates_3564_);
lean_ctor_set(v_reuseFailAlloc_3577_, 12, v_codeQualityEntryTasks_3565_);
v___x_3572_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3573_ = lean_st_ref_put(v___y_3539_, v___x_3572_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3569_);
v___x_3575_ = v___x_3546_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3569_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec(v_currNamespace_3542_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
v_a_3580_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3543_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3543_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
v_a_3588_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3540_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3540_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3596_:
{
lean_object* v_fileName_3602_; lean_object* v_fileMap_3603_; uint8_t v_suppressElabErrors_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___f_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3623_; 
v_fileName_3602_ = lean_ctor_get(v___y_3528_, 0);
v_fileMap_3603_ = lean_ctor_get(v___y_3528_, 1);
v_suppressElabErrors_3604_ = lean_ctor_get_uint8(v___y_3528_, sizeof(void*)*10);
v___x_3605_ = lean_box(v_suppressElabErrors_3604_);
v___x_3606_ = lean_box(v___y_3597_);
v___f_3607_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3607_, 0, v___x_3605_);
lean_closure_set(v___f_3607_, 1, v___x_3606_);
v___x_3608_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3525_);
v___x_3609_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v___x_3608_, v___y_3529_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3623_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3623_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_inc_ref_n(v_fileMap_3603_, 2);
v___x_3614_ = l_Lean_FileMap_toPosition(v_fileMap_3603_, v___y_3600_);
lean_dec(v___y_3600_);
v___x_3615_ = l_Lean_FileMap_toPosition(v_fileMap_3603_, v___y_3601_);
lean_dec(v___y_3601_);
v___x_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
v___x_3617_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_suppressElabErrors_3604_ == 0)
{
lean_del_object(v___x_3612_);
lean_dec_ref(v___f_3607_);
v___y_3532_ = v___x_3617_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3598_;
v___y_3535_ = v_fileName_3602_;
v___y_3536_ = v_a_3610_;
v___y_3537_ = v___x_3616_;
v___y_3538_ = v___x_3614_;
v___y_3539_ = v___y_3529_;
goto v___jp_3531_;
}
else
{
uint8_t v___x_3618_; 
lean_inc(v_a_3610_);
v___x_3618_ = l_Lean_MessageData_hasTag(v___f_3607_, v_a_3610_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3616_, 1);
lean_dec_ref(v___x_3614_);
lean_dec(v_a_3610_);
v___x_3619_ = lean_box(0);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3619_);
v___x_3621_ = v___x_3612_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
else
{
lean_del_object(v___x_3612_);
v___y_3532_ = v___x_3617_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3598_;
v___y_3535_ = v_fileName_3602_;
v___y_3536_ = v_a_3610_;
v___y_3537_ = v___x_3616_;
v___y_3538_ = v___x_3614_;
v___y_3539_ = v___y_3529_;
goto v___jp_3531_;
}
}
}
}
v___jp_3624_:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_Syntax_getTailPos_x3f(v___y_3626_, v___y_3628_);
lean_dec(v___y_3626_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_inc(v___y_3629_);
v___y_3597_ = v___y_3625_;
v___y_3598_ = v___y_3628_;
v___y_3599_ = v___y_3627_;
v___y_3600_ = v___y_3629_;
v___y_3601_ = v___y_3629_;
goto v___jp_3596_;
}
else
{
lean_object* v_val_3631_; 
v_val_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_val_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v___y_3597_ = v___y_3625_;
v___y_3598_ = v___y_3628_;
v___y_3599_ = v___y_3627_;
v___y_3600_ = v___y_3629_;
v___y_3601_ = v_val_3631_;
goto v___jp_3596_;
}
}
v___jp_3632_:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Elab_Command_getRef___redArg(v___y_3528_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v_ref_3638_; lean_object* v___x_3639_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v_ref_3638_ = l_Lean_replaceRef(v_ref_3524_, v_a_3637_);
lean_dec(v_a_3637_);
v___x_3639_ = l_Lean_Syntax_getPos_x3f(v_ref_3638_, v___y_3634_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_unsigned_to_nat(0u);
v___y_3625_ = v___y_3633_;
v___y_3626_ = v_ref_3638_;
v___y_3627_ = v___y_3635_;
v___y_3628_ = v___y_3634_;
v___y_3629_ = v___x_3640_;
goto v___jp_3624_;
}
else
{
lean_object* v_val_3641_; 
v_val_3641_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v___x_3639_, 1);
v___y_3625_ = v___y_3633_;
v___y_3626_ = v_ref_3638_;
v___y_3627_ = v___y_3635_;
v___y_3628_ = v___y_3634_;
v___y_3629_ = v_val_3641_;
goto v___jp_3624_;
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_msgData_3525_);
v_a_3642_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3636_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3636_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
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
v___jp_3651_:
{
if (v___y_3654_ == 0)
{
v___y_3633_ = v___y_3652_;
v___y_3634_ = v___y_3653_;
v___y_3635_ = v_severity_3526_;
goto v___jp_3632_;
}
else
{
v___y_3633_ = v___y_3652_;
v___y_3634_ = v___y_3653_;
v___y_3635_ = v___x_3650_;
goto v___jp_3632_;
}
}
v___jp_3655_:
{
if (v___y_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_scopes_3659_; lean_object* v___x_3660_; lean_object* v_opts_3661_; uint8_t v___x_3662_; uint8_t v___x_3663_; 
v___x_3657_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3658_ = lean_st_ref_get(v___y_3529_);
v_scopes_3659_ = lean_ctor_get(v___x_3658_, 2);
lean_inc(v_scopes_3659_);
lean_dec(v___x_3658_);
v___x_3660_ = l_List_head_x21___redArg(v___x_3657_, v_scopes_3659_);
lean_dec(v_scopes_3659_);
v_opts_3661_ = lean_ctor_get(v___x_3660_, 1);
lean_inc_ref(v_opts_3661_);
lean_dec(v___x_3660_);
v___x_3662_ = 1;
v___x_3663_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3526_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_dec_ref(v_opts_3661_);
v___y_3652_ = v___y_3656_;
v___y_3653_ = v___y_3656_;
v___y_3654_ = v___x_3663_;
goto v___jp_3651_;
}
else
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3664_ = l_Lean_warningAsError;
v___x_3665_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_3661_, v___x_3664_);
lean_dec_ref(v_opts_3661_);
v___y_3652_ = v___y_3656_;
v___y_3653_ = v___y_3656_;
v___y_3654_ = v___x_3665_;
goto v___jp_3651_;
}
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_dec_ref(v_msgData_3525_);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_3670_, lean_object* v_msgData_3671_, lean_object* v_severity_3672_, lean_object* v_isSilent_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
uint8_t v_severity_boxed_3677_; uint8_t v_isSilent_boxed_3678_; lean_object* v_res_3679_; 
v_severity_boxed_3677_ = lean_unbox(v_severity_3672_);
v_isSilent_boxed_3678_ = lean_unbox(v_isSilent_3673_);
v_res_3679_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3670_, v_msgData_3671_, v_severity_boxed_3677_, v_isSilent_boxed_3678_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v_ref_3670_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_3680_, uint8_t v_severity_3681_, uint8_t v_isSilent_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Elab_Command_getRef___redArg(v___y_3683_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___x_3688_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_3687_, v_msgData_3680_, v_severity_3681_, v_isSilent_3682_, v___y_3683_, v___y_3684_);
lean_dec(v_a_3687_);
return v___x_3688_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec_ref(v_msgData_3680_);
v_a_3689_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3686_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3686_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_3697_, lean_object* v_severity_3698_, lean_object* v_isSilent_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v_severity_boxed_3703_; uint8_t v_isSilent_boxed_3704_; lean_object* v_res_3705_; 
v_severity_boxed_3703_ = lean_unbox(v_severity_3698_);
v_isSilent_boxed_3704_ = lean_unbox(v_isSilent_3699_);
v_res_3705_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3697_, v_severity_boxed_3703_, v_isSilent_boxed_3704_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; 
v___x_3710_ = 0;
v___x_3711_ = 0;
v___x_3712_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3706_, v___x_3710_, v___x_3711_, v___y_3707_, v___y_3708_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_3718_, lean_object* v_x_3719_){
_start:
{
if (lean_obj_tag(v_x_3719_) == 0)
{
lean_object* v_k_3721_; lean_object* v_v_3722_; lean_object* v_l_3723_; lean_object* v_r_3724_; lean_object* v___x_3725_; lean_object* v_a_3726_; lean_object* v_a_3727_; lean_object* v___x_3728_; 
v_k_3721_ = lean_ctor_get(v_x_3719_, 1);
lean_inc(v_k_3721_);
v_v_3722_ = lean_ctor_get(v_x_3719_, 2);
lean_inc(v_v_3722_);
v_l_3723_ = lean_ctor_get(v_x_3719_, 3);
lean_inc(v_l_3723_);
v_r_3724_ = lean_ctor_get(v_x_3719_, 4);
lean_inc(v_r_3724_);
lean_dec_ref_known(v_x_3719_, 5);
v___x_3725_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3718_, v_l_3723_);
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref(v___x_3725_);
v_a_3727_ = lean_ctor_get(v_a_3726_, 0);
lean_inc(v_a_3727_);
lean_dec(v_a_3726_);
v___x_3728_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3721_, v_v_3722_, v_a_3727_);
v_init_3718_ = v___x_3728_;
v_x_3719_ = v_r_3724_;
goto _start;
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v_init_3718_);
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_3732_, lean_object* v_x_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3732_, v_x_3733_);
return v_res_3735_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_3736_, lean_object* v_x1_3737_, lean_object* v_x2_3738_){
_start:
{
lean_object* v_fst_3739_; lean_object* v_fst_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_fst_3739_ = lean_ctor_get(v_x1_3737_, 0);
lean_inc(v_fst_3739_);
lean_dec_ref(v_x1_3737_);
v_fst_3740_ = lean_ctor_get(v_x2_3738_, 0);
lean_inc(v_fst_3740_);
lean_dec_ref(v_x2_3738_);
v___x_3741_ = l_Lean_Name_toString(v_fst_3739_, v___x_3736_);
v___x_3742_ = l_Lean_Name_toString(v_fst_3740_, v___x_3736_);
v___x_3743_ = lean_string_dec_lt(v___x_3741_, v___x_3742_);
lean_dec_ref(v___x_3742_);
lean_dec_ref(v___x_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_3744_, lean_object* v_x1_3745_, lean_object* v_x2_3746_){
_start:
{
uint8_t v___x_18303__boxed_3747_; uint8_t v_res_3748_; lean_object* v_r_3749_; 
v___x_18303__boxed_3747_ = lean_unbox(v___x_3744_);
v_res_3748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18303__boxed_3747_, v_x1_3745_, v_x2_3746_);
v_r_3749_ = lean_box(v_res_3748_);
return v_r_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_3750_, lean_object* v_pivot_3751_, lean_object* v_as_3752_, lean_object* v_i_3753_, lean_object* v_k_3754_){
_start:
{
uint8_t v___x_3755_; 
v___x_3755_ = lean_nat_dec_lt(v_k_3754_, v_hi_3750_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec(v_k_3754_);
lean_dec_ref(v_pivot_3751_);
v___x_3756_ = lean_array_fswap(v_as_3752_, v_i_3753_, v_hi_3750_);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_i_3753_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
return v___x_3757_;
}
else
{
lean_object* v___x_3758_; lean_object* v_fst_3759_; lean_object* v_fst_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3758_ = lean_array_fget_borrowed(v_as_3752_, v_k_3754_);
v_fst_3759_ = lean_ctor_get(v___x_3758_, 0);
v_fst_3760_ = lean_ctor_get(v_pivot_3751_, 0);
lean_inc(v_fst_3759_);
v___x_3761_ = l_Lean_Name_toString(v_fst_3759_, v___x_3755_);
lean_inc(v_fst_3760_);
v___x_3762_ = l_Lean_Name_toString(v_fst_3760_, v___x_3755_);
v___x_3763_ = lean_string_dec_lt(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3762_);
lean_dec_ref(v___x_3761_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_unsigned_to_nat(1u);
v___x_3765_ = lean_nat_add(v_k_3754_, v___x_3764_);
lean_dec(v_k_3754_);
v_k_3754_ = v___x_3765_;
goto _start;
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3767_ = lean_array_fswap(v_as_3752_, v_i_3753_, v_k_3754_);
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_nat_add(v_i_3753_, v___x_3768_);
lean_dec(v_i_3753_);
v___x_3770_ = lean_nat_add(v_k_3754_, v___x_3768_);
lean_dec(v_k_3754_);
v_as_3752_ = v___x_3767_;
v_i_3753_ = v___x_3769_;
v_k_3754_ = v___x_3770_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_3772_, lean_object* v_pivot_3773_, lean_object* v_as_3774_, lean_object* v_i_3775_, lean_object* v_k_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3772_, v_pivot_3773_, v_as_3774_, v_i_3775_, v_k_3776_);
lean_dec(v_hi_3772_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_3778_, lean_object* v_as_3779_, lean_object* v_lo_3780_, lean_object* v_hi_3781_){
_start:
{
lean_object* v___y_3783_; uint8_t v___x_3793_; 
v___x_3793_ = lean_nat_dec_lt(v_lo_3780_, v_hi_3781_);
if (v___x_3793_ == 0)
{
lean_dec(v_lo_3780_);
return v_as_3779_;
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v_mid_3796_; lean_object* v___y_3798_; lean_object* v___y_3804_; lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3794_ = lean_nat_add(v_lo_3780_, v_hi_3781_);
v___x_3795_ = lean_unsigned_to_nat(1u);
v_mid_3796_ = lean_nat_shiftr(v___x_3794_, v___x_3795_);
lean_dec(v___x_3794_);
v___x_3809_ = lean_array_fget_borrowed(v_as_3779_, v_mid_3796_);
v___x_3810_ = lean_array_fget_borrowed(v_as_3779_, v_lo_3780_);
lean_inc(v___x_3810_);
lean_inc(v___x_3809_);
v___x_3811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3793_, v___x_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
v___y_3804_ = v_as_3779_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_array_fswap(v_as_3779_, v_lo_3780_, v_mid_3796_);
v___y_3804_ = v___x_3812_;
goto v___jp_3803_;
}
v___jp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = lean_array_fget_borrowed(v___y_3798_, v_mid_3796_);
v___x_3800_ = lean_array_fget_borrowed(v___y_3798_, v_hi_3781_);
lean_inc(v___x_3800_);
lean_inc(v___x_3799_);
v___x_3801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3793_, v___x_3799_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_dec(v_mid_3796_);
v___y_3783_ = v___y_3798_;
goto v___jp_3782_;
}
else
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_array_fswap(v___y_3798_, v_mid_3796_, v_hi_3781_);
lean_dec(v_mid_3796_);
v___y_3783_ = v___x_3802_;
goto v___jp_3782_;
}
}
v___jp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = lean_array_fget_borrowed(v___y_3804_, v_hi_3781_);
v___x_3806_ = lean_array_fget_borrowed(v___y_3804_, v_lo_3780_);
lean_inc(v___x_3806_);
lean_inc(v___x_3805_);
v___x_3807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3793_, v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
v___y_3798_ = v___y_3804_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_array_fswap(v___y_3804_, v_lo_3780_, v_hi_3781_);
v___y_3798_ = v___x_3808_;
goto v___jp_3797_;
}
}
}
v___jp_3782_:
{
lean_object* v_pivot_3784_; lean_object* v___x_3785_; lean_object* v_fst_3786_; lean_object* v_snd_3787_; uint8_t v___x_3788_; 
v_pivot_3784_ = lean_array_fget(v___y_3783_, v_hi_3781_);
lean_inc_n(v_lo_3780_, 2);
v___x_3785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3781_, v_pivot_3784_, v___y_3783_, v_lo_3780_, v_lo_3780_);
v_fst_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_fst_3786_);
v_snd_3787_ = lean_ctor_get(v___x_3785_, 1);
lean_inc(v_snd_3787_);
lean_dec_ref(v___x_3785_);
v___x_3788_ = lean_nat_dec_le(v_hi_3781_, v_fst_3786_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3778_, v_snd_3787_, v_lo_3780_, v_fst_3786_);
v___x_3790_ = lean_unsigned_to_nat(1u);
v___x_3791_ = lean_nat_add(v_fst_3786_, v___x_3790_);
lean_dec(v_fst_3786_);
v_as_3779_ = v___x_3789_;
v_lo_3780_ = v___x_3791_;
goto _start;
}
else
{
lean_dec(v_fst_3786_);
lean_dec(v_lo_3780_);
return v_snd_3787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_3813_, lean_object* v_as_3814_, lean_object* v_lo_3815_, lean_object* v_hi_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3813_, v_as_3814_, v_lo_3815_, v_hi_3816_);
lean_dec(v_hi_3816_);
lean_dec(v_n_3813_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_3818_, lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3819_) == 0)
{
lean_object* v_k_3820_; lean_object* v_v_3821_; lean_object* v_l_3822_; lean_object* v_r_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_k_3820_ = lean_ctor_get(v_x_3819_, 1);
v_v_3821_ = lean_ctor_get(v_x_3819_, 2);
v_l_3822_ = lean_ctor_get(v_x_3819_, 3);
v_r_3823_ = lean_ctor_get(v_x_3819_, 4);
v___x_3824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3818_, v_l_3822_);
lean_inc(v_v_3821_);
lean_inc(v_k_3820_);
v___x_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3825_, 0, v_k_3820_);
lean_ctor_set(v___x_3825_, 1, v_v_3821_);
v___x_3826_ = lean_array_push(v___x_3824_, v___x_3825_);
v_init_3818_ = v___x_3826_;
v_x_3819_ = v_r_3823_;
goto _start;
}
else
{
return v_init_3818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_3828_, lean_object* v_x_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3828_, v_x_3829_);
lean_dec(v_x_3829_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_3831_, size_t v_sz_3832_, size_t v_i_3833_, lean_object* v_b_3834_){
_start:
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_usize_dec_lt(v_i_3833_, v_sz_3832_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_b_3834_);
return v___x_3837_;
}
else
{
lean_object* v_a_3838_; lean_object* v_fst_3839_; lean_object* v_snd_3840_; lean_object* v_found_3841_; size_t v___x_3842_; size_t v___x_3843_; 
v_a_3838_ = lean_array_uget_borrowed(v_as_3831_, v_i_3833_);
v_fst_3839_ = lean_ctor_get(v_a_3838_, 0);
v_snd_3840_ = lean_ctor_get(v_a_3838_, 1);
lean_inc(v_snd_3840_);
lean_inc(v_fst_3839_);
v_found_3841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3839_, v_snd_3840_, v_b_3834_);
v___x_3842_ = ((size_t)1ULL);
v___x_3843_ = lean_usize_add(v_i_3833_, v___x_3842_);
v_i_3833_ = v___x_3843_;
v_b_3834_ = v_found_3841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_3845_, lean_object* v_sz_3846_, lean_object* v_i_3847_, lean_object* v_b_3848_, lean_object* v___y_3849_){
_start:
{
size_t v_sz_boxed_3850_; size_t v_i_boxed_3851_; lean_object* v_res_3852_; 
v_sz_boxed_3850_ = lean_unbox_usize(v_sz_3846_);
lean_dec(v_sz_3846_);
v_i_boxed_3851_ = lean_unbox_usize(v_i_3847_);
lean_dec(v_i_3847_);
v_res_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3845_, v_sz_boxed_3850_, v_i_boxed_3851_, v_b_3848_);
lean_dec_ref(v_as_3845_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3853_, size_t v_sz_3854_, size_t v_i_3855_, lean_object* v_b_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
uint8_t v___x_3860_; 
v___x_3860_ = lean_usize_dec_lt(v_i_3855_, v_sz_3854_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_b_3856_);
return v___x_3861_;
}
else
{
lean_object* v_a_3862_; size_t v_sz_3863_; size_t v___x_3864_; lean_object* v___x_3865_; 
v_a_3862_ = lean_array_uget_borrowed(v_as_3853_, v_i_3855_);
v_sz_3863_ = lean_array_size(v_a_3862_);
v___x_3864_ = ((size_t)0ULL);
v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_3862_, v_sz_3863_, v___x_3864_, v_b_3856_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; size_t v___x_3867_; size_t v___x_3868_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3865_, 1);
v___x_3867_ = ((size_t)1ULL);
v___x_3868_ = lean_usize_add(v_i_3855_, v___x_3867_);
v_i_3855_ = v___x_3868_;
v_b_3856_ = v_a_3866_;
goto _start;
}
else
{
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3870_, lean_object* v_sz_3871_, lean_object* v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
size_t v_sz_boxed_3877_; size_t v_i_boxed_3878_; lean_object* v_res_3879_; 
v_sz_boxed_3877_ = lean_unbox_usize(v_sz_3871_);
lean_dec(v_sz_3871_);
v_i_boxed_3878_ = lean_unbox_usize(v_i_3872_);
lean_dec(v_i_3872_);
v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3870_, v_sz_boxed_3877_, v_i_boxed_3878_, v_b_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v_as_3870_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___y_3886_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_env_3904_; lean_object* v___x_3905_; lean_object* v_toEnvExtension_3906_; lean_object* v_asyncMode_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; lean_object* v_a_3911_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v_a_3936_; lean_object* v_a_3937_; 
v___x_3901_ = lean_box(1);
v___x_3902_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3903_ = lean_st_ref_get(v___y_3883_);
v_env_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc_ref_n(v_env_3904_, 2);
lean_dec(v___x_3903_);
v___x_3905_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_3906_ = lean_ctor_get(v___x_3905_, 0);
v_asyncMode_3907_ = lean_ctor_get(v_toEnvExtension_3906_, 2);
v___x_3908_ = lean_box(0);
v___x_3909_ = 0;
v___x_3934_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3901_, v___x_3905_, v_env_3904_, v_asyncMode_3907_, v___x_3908_, v___x_3909_);
v___x_3935_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_3901_, v___x_3934_);
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref(v___x_3935_);
v_a_3937_ = lean_ctor_get(v_a_3936_, 0);
lean_inc(v_a_3937_);
lean_dec(v_a_3936_);
v_a_3911_ = v_a_3937_;
goto v___jp_3910_;
v___jp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_array_to_list(v___y_3886_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
return v___x_3888_;
}
v___jp_3889_:
{
lean_object* v___x_3894_; 
v___x_3894_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_3890_, v___y_3892_, v___y_3891_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec(v___y_3890_);
v___y_3886_ = v___x_3894_;
goto v___jp_3885_;
}
v___jp_3895_:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_nat_dec_le(v___y_3899_, v___y_3898_);
if (v___x_3900_ == 0)
{
lean_dec(v___y_3898_);
lean_inc(v___y_3899_);
v___y_3890_ = v___y_3896_;
v___y_3891_ = v___y_3899_;
v___y_3892_ = v___y_3897_;
v___y_3893_ = v___y_3899_;
goto v___jp_3889_;
}
else
{
v___y_3890_ = v___y_3896_;
v___y_3891_ = v___y_3899_;
v___y_3892_ = v___y_3897_;
v___y_3893_ = v___y_3898_;
goto v___jp_3889_;
}
}
v___jp_3910_:
{
lean_object* v___x_3912_; lean_object* v_importedEntries_3913_; size_t v_sz_3914_; size_t v___x_3915_; lean_object* v___x_3916_; 
v___x_3912_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3902_, v_toEnvExtension_3906_, v_env_3904_, v_asyncMode_3907_, v___x_3908_, v___x_3909_);
v_importedEntries_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc_ref(v_importedEntries_3913_);
lean_dec(v___x_3912_);
v_sz_3914_ = lean_array_size(v_importedEntries_3913_);
v___x_3915_ = ((size_t)0ULL);
v___x_3916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_3913_, v_sz_3914_, v___x_3915_, v_a_3911_, v___y_3882_, v___y_3883_);
lean_dec_ref(v_importedEntries_3913_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v_arr_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_3920_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_3919_, v_a_3917_);
lean_dec(v_a_3917_);
v___x_3921_ = lean_array_get_size(v_arr_3920_);
v___x_3922_ = lean_nat_dec_eq(v___x_3921_, v___x_3918_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_sub(v___x_3921_, v___x_3923_);
v___x_3925_ = lean_nat_dec_le(v___x_3918_, v___x_3924_);
if (v___x_3925_ == 0)
{
lean_inc(v___x_3924_);
v___y_3896_ = v___x_3921_;
v___y_3897_ = v_arr_3920_;
v___y_3898_ = v___x_3924_;
v___y_3899_ = v___x_3924_;
goto v___jp_3895_;
}
else
{
v___y_3896_ = v___x_3921_;
v___y_3897_ = v_arr_3920_;
v___y_3898_ = v___x_3924_;
v___y_3899_ = v___x_3918_;
goto v___jp_3895_;
}
}
else
{
v___y_3886_ = v_arr_3920_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
v_a_3926_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3916_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3916_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_3942_, lean_object* v_k_3943_, lean_object* v_fallback_3944_){
_start:
{
if (lean_obj_tag(v_t_3942_) == 0)
{
lean_object* v_k_3945_; lean_object* v_v_3946_; lean_object* v_l_3947_; lean_object* v_r_3948_; uint8_t v___x_3949_; 
v_k_3945_ = lean_ctor_get(v_t_3942_, 1);
v_v_3946_ = lean_ctor_get(v_t_3942_, 2);
v_l_3947_ = lean_ctor_get(v_t_3942_, 3);
v_r_3948_ = lean_ctor_get(v_t_3942_, 4);
v___x_3949_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3943_, v_k_3945_);
switch(v___x_3949_)
{
case 0:
{
v_t_3942_ = v_l_3947_;
goto _start;
}
case 1:
{
lean_inc(v_v_3946_);
return v_v_3946_;
}
default: 
{
v_t_3942_ = v_r_3948_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3944_);
return v_fallback_3944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_3952_, lean_object* v_k_3953_, lean_object* v_fallback_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3952_, v_k_3953_, v_fallback_3954_);
lean_dec(v_fallback_3954_);
lean_dec(v_k_3953_);
lean_dec(v_t_3952_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_3956_, size_t v_sz_3957_, size_t v_i_3958_, lean_object* v_b_3959_){
_start:
{
uint8_t v___x_3961_; 
v___x_3961_ = lean_usize_dec_lt(v_i_3958_, v_sz_3957_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; 
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v_b_3959_);
return v___x_3962_;
}
else
{
lean_object* v_a_3963_; lean_object* v_fst_3964_; lean_object* v_snd_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; size_t v___x_3970_; size_t v___x_3971_; 
v_a_3963_ = lean_array_uget_borrowed(v_as_3956_, v_i_3958_);
v_fst_3964_ = lean_ctor_get(v_a_3963_, 0);
v_snd_3965_ = lean_ctor_get(v_a_3963_, 1);
v___x_3966_ = l_Lean_NameSet_empty;
v___x_3967_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3959_, v_snd_3965_, v___x_3966_);
lean_inc(v_fst_3964_);
v___x_3968_ = l_Lean_NameSet_insert(v___x_3967_, v_fst_3964_);
lean_inc(v_snd_3965_);
v___x_3969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_3965_, v___x_3968_, v_b_3959_);
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_add(v_i_3958_, v___x_3970_);
v_i_3958_ = v___x_3971_;
v_b_3959_ = v___x_3969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_3973_, lean_object* v_sz_3974_, lean_object* v_i_3975_, lean_object* v_b_3976_, lean_object* v___y_3977_){
_start:
{
size_t v_sz_boxed_3978_; size_t v_i_boxed_3979_; lean_object* v_res_3980_; 
v_sz_boxed_3978_ = lean_unbox_usize(v_sz_3974_);
lean_dec(v_sz_3974_);
v_i_boxed_3979_ = lean_unbox_usize(v_i_3975_);
lean_dec(v_i_3975_);
v_res_3980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3973_, v_sz_boxed_3978_, v_i_boxed_3979_, v_b_3976_);
lean_dec_ref(v_as_3973_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_3981_, size_t v_sz_3982_, size_t v_i_3983_, lean_object* v_b_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_usize_dec_lt(v_i_3983_, v_sz_3982_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_b_3984_);
return v___x_3989_;
}
else
{
lean_object* v_a_3990_; size_t v_sz_3991_; size_t v___x_3992_; lean_object* v___x_3993_; 
v_a_3990_ = lean_array_uget_borrowed(v_as_3981_, v_i_3983_);
v_sz_3991_ = lean_array_size(v_a_3990_);
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_3990_, v_sz_3991_, v___x_3992_, v_b_3984_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; size_t v___x_3995_; size_t v___x_3996_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3993_, 1);
v___x_3995_ = ((size_t)1ULL);
v___x_3996_ = lean_usize_add(v_i_3983_, v___x_3995_);
v_i_3983_ = v___x_3996_;
v_b_3984_ = v_a_3994_;
goto _start;
}
else
{
return v___x_3993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_3998_, lean_object* v_sz_3999_, lean_object* v_i_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
size_t v_sz_boxed_4005_; size_t v_i_boxed_4006_; lean_object* v_res_4007_; 
v_sz_boxed_4005_ = lean_unbox_usize(v_sz_3999_);
lean_dec(v_sz_3999_);
v_i_boxed_4006_ = lean_unbox_usize(v_i_4000_);
lean_dec(v_i_4000_);
v_res_4007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_3998_, v_sz_boxed_4005_, v_i_boxed_4006_, v_b_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec_ref(v_as_3998_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_4008_, size_t v_i_4009_, size_t v_stop_4010_, lean_object* v_b_4011_){
_start:
{
uint8_t v___x_4012_; 
v___x_4012_ = lean_usize_dec_eq(v_i_4009_, v_stop_4010_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; lean_object* v_fst_4014_; lean_object* v_snd_4015_; lean_object* v___x_4016_; size_t v___x_4017_; size_t v___x_4018_; 
v___x_4013_ = lean_array_uget_borrowed(v_as_4008_, v_i_4009_);
v_fst_4014_ = lean_ctor_get(v___x_4013_, 0);
v_snd_4015_ = lean_ctor_get(v___x_4013_, 1);
lean_inc(v_snd_4015_);
lean_inc(v_fst_4014_);
v___x_4016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4014_, v_snd_4015_, v_b_4011_);
v___x_4017_ = ((size_t)1ULL);
v___x_4018_ = lean_usize_add(v_i_4009_, v___x_4017_);
v_i_4009_ = v___x_4018_;
v_b_4011_ = v___x_4016_;
goto _start;
}
else
{
return v_b_4011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_4020_, lean_object* v_i_4021_, lean_object* v_stop_4022_, lean_object* v_b_4023_){
_start:
{
size_t v_i_boxed_4024_; size_t v_stop_boxed_4025_; lean_object* v_res_4026_; 
v_i_boxed_4024_ = lean_unbox_usize(v_i_4021_);
lean_dec(v_i_4021_);
v_stop_boxed_4025_ = lean_unbox_usize(v_stop_4022_);
lean_dec(v_stop_4022_);
v_res_4026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_4020_, v_i_boxed_4024_, v_stop_boxed_4025_, v_b_4023_);
lean_dec_ref(v_as_4020_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_4027_, size_t v_i_4028_, size_t v_stop_4029_, lean_object* v_b_4030_){
_start:
{
lean_object* v___y_4032_; uint8_t v___x_4036_; 
v___x_4036_ = lean_usize_dec_eq(v_i_4028_, v_stop_4029_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4037_ = lean_array_uget_borrowed(v_as_4027_, v_i_4028_);
v___x_4038_ = lean_unsigned_to_nat(0u);
v___x_4039_ = lean_array_get_size(v___x_4037_);
v___x_4040_ = lean_nat_dec_lt(v___x_4038_, v___x_4039_);
if (v___x_4040_ == 0)
{
v___y_4032_ = v_b_4030_;
goto v___jp_4031_;
}
else
{
size_t v___x_4041_; size_t v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = ((size_t)0ULL);
v___x_4042_ = lean_usize_of_nat(v___x_4039_);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_4037_, v___x_4041_, v___x_4042_, v_b_4030_);
v___y_4032_ = v___x_4043_;
goto v___jp_4031_;
}
}
else
{
return v_b_4030_;
}
v___jp_4031_:
{
size_t v___x_4033_; size_t v___x_4034_; 
v___x_4033_ = ((size_t)1ULL);
v___x_4034_ = lean_usize_add(v_i_4028_, v___x_4033_);
v_i_4028_ = v___x_4034_;
v_b_4030_ = v___y_4032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_4044_, lean_object* v_i_4045_, lean_object* v_stop_4046_, lean_object* v_b_4047_){
_start:
{
size_t v_i_boxed_4048_; size_t v_stop_boxed_4049_; lean_object* v_res_4050_; 
v_i_boxed_4048_ = lean_unbox_usize(v_i_4045_);
lean_dec(v_i_4045_);
v_stop_boxed_4049_ = lean_unbox_usize(v_stop_4046_);
lean_dec(v_stop_4046_);
v_res_4050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_4044_, v_i_boxed_4048_, v_stop_boxed_4049_, v_b_4047_);
lean_dec_ref(v_as_4044_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_4051_){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v_env_4057_; lean_object* v___x_4058_; lean_object* v_ext_4059_; lean_object* v_toEnvExtension_4060_; lean_object* v_asyncMode_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v_categories_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4053_ = lean_box(1);
v___x_4054_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4055_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4056_ = lean_st_ref_get(v___y_4051_);
v_env_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc_ref_n(v_env_4057_, 2);
lean_dec(v___x_4056_);
v___x_4058_ = l_Lean_Parser_parserExtension;
v_ext_4059_ = lean_ctor_get(v___x_4058_, 1);
v_toEnvExtension_4060_ = lean_ctor_get(v_ext_4059_, 0);
v_asyncMode_4061_ = lean_ctor_get(v_toEnvExtension_4060_, 2);
v___x_4062_ = 0;
v___x_4063_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4055_, v___x_4058_, v_env_4057_, v_asyncMode_4061_, v___x_4062_);
v_categories_4064_ = lean_ctor_get(v___x_4063_, 2);
lean_inc_ref(v_categories_4064_);
lean_dec(v___x_4063_);
v___x_4065_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4066_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4064_, v___x_4065_);
lean_dec_ref(v_categories_4064_);
if (lean_obj_tag(v___x_4066_) == 1)
{
lean_object* v_val_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4098_; 
v_val_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4098_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_val_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4098_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___y_4072_; lean_object* v___x_4081_; lean_object* v_toEnvExtension_4082_; lean_object* v_exportEntriesFn_4083_; lean_object* v_asyncMode_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v_importedEntries_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v_exported_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4081_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4082_ = lean_ctor_get(v___x_4081_, 0);
v_exportEntriesFn_4083_ = lean_ctor_get(v___x_4081_, 4);
v_asyncMode_4084_ = lean_ctor_get(v_toEnvExtension_4082_, 2);
v___x_4085_ = lean_box(0);
lean_inc_ref_n(v_env_4057_, 2);
v___x_4086_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4054_, v_toEnvExtension_4082_, v_env_4057_, v_asyncMode_4084_, v___x_4085_, v___x_4062_);
v_importedEntries_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc_ref(v_importedEntries_4087_);
lean_dec(v___x_4086_);
v___x_4088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4053_, v___x_4081_, v_env_4057_, v_asyncMode_4084_, v___x_4085_, v___x_4062_);
lean_inc_ref(v_exportEntriesFn_4083_);
v___x_4089_ = lean_apply_2(v_exportEntriesFn_4083_, v_env_4057_, v___x_4088_);
v_exported_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_exported_4090_);
lean_dec_ref(v___x_4089_);
v___x_4091_ = lean_array_push(v_importedEntries_4087_, v_exported_4090_);
v___x_4092_ = lean_unsigned_to_nat(0u);
v___x_4093_ = lean_array_get_size(v___x_4091_);
v___x_4094_ = lean_nat_dec_lt(v___x_4092_, v___x_4093_);
if (v___x_4094_ == 0)
{
lean_dec_ref(v___x_4091_);
v___y_4072_ = v___x_4053_;
goto v___jp_4071_;
}
else
{
size_t v___x_4095_; size_t v___x_4096_; lean_object* v___x_4097_; 
v___x_4095_ = ((size_t)0ULL);
v___x_4096_ = lean_usize_of_nat(v___x_4093_);
v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4091_, v___x_4095_, v___x_4096_, v___x_4053_);
lean_dec_ref(v___x_4091_);
v___y_4072_ = v___x_4097_;
goto v___jp_4071_;
}
v___jp_4071_:
{
lean_object* v_tables_4073_; lean_object* v_leadingTable_4074_; lean_object* v_trailingTable_4075_; lean_object* v_firstTokens_4076_; lean_object* v_firstTokens_4077_; lean_object* v___x_4079_; 
v_tables_4073_ = lean_ctor_get(v_val_4067_, 2);
v_leadingTable_4074_ = lean_ctor_get(v_tables_4073_, 0);
v_trailingTable_4075_ = lean_ctor_get(v_tables_4073_, 2);
lean_inc(v_trailingTable_4075_);
lean_inc(v_leadingTable_4074_);
lean_inc(v_val_4067_);
v_firstTokens_4076_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4067_, v_leadingTable_4074_, v___y_4072_);
v_firstTokens_4077_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4067_, v_trailingTable_4075_, v_firstTokens_4076_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set_tag(v___x_4069_, 0);
lean_ctor_set(v___x_4069_, 0, v_firstTokens_4077_);
v___x_4079_ = v___x_4069_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_firstTokens_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v___x_4099_; 
lean_dec(v___x_4066_);
lean_dec_ref(v_env_4057_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4053_);
return v___x_4099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4100_);
lean_dec(v___y_4100_);
return v_res_4102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v_env_4112_; lean_object* v___x_4113_; lean_object* v_env_4114_; lean_object* v___x_4115_; lean_object* v_env_4116_; lean_object* v___x_4117_; lean_object* v_toEnvExtension_4118_; lean_object* v_exportEntriesFn_4119_; lean_object* v_asyncMode_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v_importedEntries_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4176_; 
v___x_4109_ = lean_box(1);
v___x_4110_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4111_ = lean_st_ref_get(v_a_4107_);
v_env_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc_ref(v_env_4112_);
lean_dec(v___x_4111_);
v___x_4113_ = lean_st_ref_get(v_a_4107_);
v_env_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc_ref(v_env_4114_);
lean_dec(v___x_4113_);
v___x_4115_ = lean_st_ref_get(v_a_4107_);
v_env_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc_ref(v_env_4116_);
lean_dec(v___x_4115_);
v___x_4117_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4118_ = lean_ctor_get(v___x_4117_, 0);
v_exportEntriesFn_4119_ = lean_ctor_get(v___x_4117_, 4);
v_asyncMode_4120_ = lean_ctor_get(v_toEnvExtension_4118_, 2);
v___x_4121_ = lean_box(0);
v___x_4122_ = 0;
v___x_4123_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4110_, v_toEnvExtension_4118_, v_env_4112_, v_asyncMode_4120_, v___x_4121_, v___x_4122_);
v_importedEntries_4124_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4176_ == 0)
{
lean_object* v_unused_4177_; 
v_unused_4177_ = lean_ctor_get(v___x_4123_, 1);
lean_dec(v_unused_4177_);
v___x_4126_ = v___x_4123_;
v_isShared_4127_ = v_isSharedCheck_4176_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_importedEntries_4124_);
lean_dec(v___x_4123_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4176_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v_exported_4130_; lean_object* v___x_4131_; size_t v_sz_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
v___x_4128_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4109_, v___x_4117_, v_env_4116_, v_asyncMode_4120_, v___x_4121_, v___x_4122_);
lean_inc_ref(v_exportEntriesFn_4119_);
v___x_4129_ = lean_apply_2(v_exportEntriesFn_4119_, v_env_4114_, v___x_4128_);
v_exported_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_exported_4130_);
lean_dec_ref(v___x_4129_);
v___x_4131_ = lean_array_push(v_importedEntries_4124_, v_exported_4130_);
v_sz_4132_ = lean_array_size(v___x_4131_);
v___x_4133_ = ((size_t)0ULL);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_4131_, v_sz_4132_, v___x_4133_, v___x_4109_, v_a_4106_, v_a_4107_);
lean_dec_ref(v___x_4131_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4136_; lean_object* v_a_4137_; lean_object* v___x_4138_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___x_4136_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_4107_);
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref(v___x_4136_);
v___x_4138_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_4106_, v_a_4107_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = lean_box(0);
v___x_4141_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_4137_, v_a_4135_, v_a_4139_, v___x_4140_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4135_);
lean_dec(v_a_4137_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_4144_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_4145_ = l_Lean_MessageData_joinSep(v_a_4142_, v___x_4144_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set_tag(v___x_4126_, 7);
lean_ctor_set(v___x_4126_, 1, v___x_4145_);
lean_ctor_set(v___x_4126_, 0, v___x_4144_);
v___x_4147_ = v___x_4126_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4144_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = l_Lean_MessageData_nestD(v___x_4147_);
v___x_4149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4143_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
v___x_4150_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_4149_, v_a_4106_, v_a_4107_);
return v___x_4150_;
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_del_object(v___x_4126_);
v_a_4152_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4141_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4141_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec(v_a_4137_);
lean_dec(v_a_4135_);
lean_del_object(v___x_4126_);
v_a_4160_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4138_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4138_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_del_object(v___x_4126_);
v_a_4168_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4134_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4134_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4183_, v_a_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4187_, v_a_4188_, v_a_4189_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v___stx_4187_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_4192_, lean_object* v_t_4193_, lean_object* v_k_4194_, lean_object* v_fallback_4195_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4193_, v_k_4194_, v_fallback_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_4197_, lean_object* v_t_4198_, lean_object* v_k_4199_, lean_object* v_fallback_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_4197_, v_t_4198_, v_k_4199_, v_fallback_4200_);
lean_dec(v_fallback_4200_);
lean_dec(v_k_4199_);
lean_dec(v_t_4198_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_4202_, size_t v_sz_4203_, size_t v_i_4204_, lean_object* v_b_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4202_, v_sz_4203_, v_i_4204_, v_b_4205_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_4210_, lean_object* v_sz_4211_, lean_object* v_i_4212_, lean_object* v_b_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
size_t v_sz_boxed_4217_; size_t v_i_boxed_4218_; lean_object* v_res_4219_; 
v_sz_boxed_4217_ = lean_unbox_usize(v_sz_4211_);
lean_dec(v_sz_4211_);
v_i_boxed_4218_ = lean_unbox_usize(v_i_4212_);
lean_dec(v_i_4212_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4210_, v_sz_boxed_4217_, v_i_boxed_4218_, v_b_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_as_4210_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_4228_, lean_object* v___x_4229_, lean_object* v___x_4230_, lean_object* v_inst_4231_, lean_object* v_R_4232_, lean_object* v_a_4233_, lean_object* v_b_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_4228_, v___x_4229_, v___x_4230_, v_a_4233_, v_b_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_4236_, lean_object* v___x_4237_, lean_object* v___x_4238_, lean_object* v_inst_4239_, lean_object* v_R_4240_, lean_object* v_a_4241_, lean_object* v_b_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_4236_, v___x_4237_, v___x_4238_, v_inst_4239_, v_R_4240_, v_a_4241_, v_b_4242_);
lean_dec_ref(v___x_4237_);
lean_dec_ref(v_val_4236_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_4244_, lean_object* v_t_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_4244_, v_t_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_4247_, lean_object* v_as_4248_, lean_object* v_lo_4249_, lean_object* v_hi_4250_, lean_object* v_w_4251_, lean_object* v_hlo_4252_, lean_object* v_hhi_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_4247_, v_as_4248_, v_lo_4249_, v_hi_4250_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_4255_, lean_object* v_as_4256_, lean_object* v_lo_4257_, lean_object* v_hi_4258_, lean_object* v_w_4259_, lean_object* v_hlo_4260_, lean_object* v_hhi_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_4255_, v_as_4256_, v_lo_4257_, v_hi_4258_, v_w_4259_, v_hlo_4260_, v_hhi_4261_);
lean_dec(v_hi_4258_);
lean_dec(v_n_4255_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_4263_, lean_object* v_x_4264_, lean_object* v_x_4265_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_4264_, v_x_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4267_, lean_object* v_x_4268_, lean_object* v_x_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_4267_, v_x_4268_, v_x_4269_);
lean_dec(v_x_4269_);
lean_dec_ref(v_x_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_4271_, v___y_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_4281_, lean_object* v_t_4282_, lean_object* v_k_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_4282_, v_k_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_4285_, lean_object* v_t_4286_, lean_object* v_k_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_4285_, v_t_4286_, v_k_4287_);
lean_dec(v_k_4287_);
lean_dec(v_t_4286_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_4290_, v_x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_4293_, v_x_4294_, v_x_4295_);
lean_dec(v_x_4295_);
lean_dec_ref(v_x_4294_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_4297_, lean_object* v_lo_4298_, lean_object* v_hi_4299_, lean_object* v_hhi_4300_, lean_object* v_pivot_4301_, lean_object* v_as_4302_, lean_object* v_i_4303_, lean_object* v_k_4304_, lean_object* v_ilo_4305_, lean_object* v_ik_4306_, lean_object* v_w_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_4299_, v_pivot_4301_, v_as_4302_, v_i_4303_, v_k_4304_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_4309_, lean_object* v_lo_4310_, lean_object* v_hi_4311_, lean_object* v_hhi_4312_, lean_object* v_pivot_4313_, lean_object* v_as_4314_, lean_object* v_i_4315_, lean_object* v_k_4316_, lean_object* v_ilo_4317_, lean_object* v_ik_4318_, lean_object* v_w_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_4309_, v_lo_4310_, v_hi_4311_, v_hhi_4312_, v_pivot_4313_, v_as_4314_, v_i_4315_, v_k_4316_, v_ilo_4317_, v_ik_4318_, v_w_4319_);
lean_dec(v_hi_4311_);
lean_dec(v_lo_4310_);
lean_dec(v_n_4309_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_4321_, size_t v_sz_4322_, size_t v_i_4323_, lean_object* v_b_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4321_, v_sz_4322_, v_i_4323_, v_b_4324_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_4329_, lean_object* v_sz_4330_, lean_object* v_i_4331_, lean_object* v_b_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
size_t v_sz_boxed_4336_; size_t v_i_boxed_4337_; lean_object* v_res_4338_; 
v_sz_boxed_4336_ = lean_unbox_usize(v_sz_4330_);
lean_dec(v_sz_4330_);
v_i_boxed_4337_ = lean_unbox_usize(v_i_4331_);
lean_dec(v_i_4331_);
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4329_, v_sz_boxed_4336_, v_i_boxed_4337_, v_b_4332_, v___y_4333_, v___y_4334_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec_ref(v_as_4329_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_4339_, lean_object* v_t_4340_){
_start:
{
lean_object* v___x_4341_; 
v___x_4341_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4339_, v_t_4340_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_4342_, lean_object* v_t_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_4342_, v_t_4343_);
lean_dec(v_t_4343_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_4345_, lean_object* v_as_4346_, lean_object* v_lo_4347_, lean_object* v_hi_4348_, lean_object* v_w_4349_, lean_object* v_hlo_4350_, lean_object* v_hhi_4351_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4345_, v_as_4346_, v_lo_4347_, v_hi_4348_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_4353_, lean_object* v_as_4354_, lean_object* v_lo_4355_, lean_object* v_hi_4356_, lean_object* v_w_4357_, lean_object* v_hlo_4358_, lean_object* v_hhi_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_4353_, v_as_4354_, v_lo_4355_, v_hi_4356_, v_w_4357_, v_hlo_4358_, v_hhi_4359_);
lean_dec(v_hi_4356_);
lean_dec(v_n_4353_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4361_, v_x_4362_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_4367_, lean_object* v_x_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4367_, v_x_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_4373_, lean_object* v_x_4374_, size_t v_x_4375_, lean_object* v_x_4376_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_4374_, v_x_4375_, v_x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4378_, lean_object* v_x_4379_, lean_object* v_x_4380_, lean_object* v_x_4381_){
_start:
{
size_t v_x_19011__boxed_4382_; lean_object* v_res_4383_; 
v_x_19011__boxed_4382_ = lean_unbox_usize(v_x_4380_);
lean_dec(v_x_4380_);
v_res_4383_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_4378_, v_x_4379_, v_x_19011__boxed_4382_, v_x_4381_);
lean_dec(v_x_4381_);
lean_dec_ref(v_x_4379_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_4384_, lean_object* v_k_4385_, lean_object* v_x_4386_, lean_object* v_x_4387_, lean_object* v_x_4388_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_4384_, v_k_4385_, v_x_4386_, v_x_4387_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_4390_, lean_object* v_k_4391_, lean_object* v_x_4392_, lean_object* v_x_4393_, lean_object* v_x_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_4390_, v_k_4391_, v_x_4392_, v_x_4393_, v_x_4394_);
lean_dec_ref(v_k_4391_);
lean_dec_ref(v_as_4390_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_4396_, lean_object* v_m_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_4397_, v_a_4398_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_4400_, lean_object* v_m_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_4400_, v_m_4401_, v_a_4402_);
lean_dec(v_a_4402_);
lean_dec_ref(v_m_4401_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_4404_, lean_object* v_lo_4405_, lean_object* v_hi_4406_, lean_object* v_hhi_4407_, lean_object* v_pivot_4408_, lean_object* v_as_4409_, lean_object* v_i_4410_, lean_object* v_k_4411_, lean_object* v_ilo_4412_, lean_object* v_ik_4413_, lean_object* v_w_4414_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4406_, v_pivot_4408_, v_as_4409_, v_i_4410_, v_k_4411_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_4416_, lean_object* v_lo_4417_, lean_object* v_hi_4418_, lean_object* v_hhi_4419_, lean_object* v_pivot_4420_, lean_object* v_as_4421_, lean_object* v_i_4422_, lean_object* v_k_4423_, lean_object* v_ilo_4424_, lean_object* v_ik_4425_, lean_object* v_w_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_4416_, v_lo_4417_, v_hi_4418_, v_hhi_4419_, v_pivot_4420_, v_as_4421_, v_i_4422_, v_k_4423_, v_ilo_4424_, v_ik_4425_, v_w_4426_);
lean_dec(v_hi_4418_);
lean_dec(v_lo_4417_);
lean_dec(v_n_4416_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_4428_, lean_object* v_keys_4429_, lean_object* v_vals_4430_, lean_object* v_heq_4431_, lean_object* v_i_4432_, lean_object* v_k_4433_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_4429_, v_vals_4430_, v_i_4432_, v_k_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_4435_, lean_object* v_keys_4436_, lean_object* v_vals_4437_, lean_object* v_heq_4438_, lean_object* v_i_4439_, lean_object* v_k_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_4435_, v_keys_4436_, v_vals_4437_, v_heq_4438_, v_i_4439_, v_k_4440_);
lean_dec(v_k_4440_);
lean_dec_ref(v_vals_4437_);
lean_dec_ref(v_keys_4436_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_4442_, lean_object* v_a_4443_, lean_object* v_x_4444_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_4443_, v_x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_4446_, lean_object* v_a_4447_, lean_object* v_x_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_4446_, v_a_4447_, v_x_4448_);
lean_dec(v_x_4448_);
lean_dec(v_a_4447_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4464_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_4466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4467_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_4468_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4464_, v___x_4465_, v___x_4466_, v___x_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_4475_ = l_Lean_addBuiltinDocString(v___x_4473_, v___x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_4506_ = l_Lean_addBuiltinDeclarationRanges(v___x_4504_, v___x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_4509_, lean_object* v___x_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, uint8_t v_includeUnnamed_4513_, lean_object* v_x_4514_, lean_object* v_____s_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_fst_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4576_; 
v_fst_4521_ = lean_ctor_get(v_x_4514_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_x_4514_);
if (v_isSharedCheck_4576_ == 0)
{
lean_object* v_unused_4577_; 
v_unused_4577_ = lean_ctor_get(v_x_4514_, 1);
lean_dec(v_unused_4577_);
v___x_4523_ = v_x_4514_;
v_isShared_4524_ = v_isSharedCheck_4576_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_fst_4521_);
lean_dec(v_x_4514_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4576_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_userName_4526_; lean_object* v___y_4527_; lean_object* v___x_4561_; 
lean_inc(v_fst_4521_);
lean_inc_ref(v_env_4509_);
v___x_4561_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4509_, v_fst_4521_);
if (lean_obj_tag(v___x_4561_) == 1)
{
lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4569_; 
lean_del_object(v___x_4523_);
lean_dec(v_fst_4521_);
lean_dec(v___x_4510_);
lean_dec_ref(v_env_4509_);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; 
v_unused_4570_ = lean_ctor_get(v___x_4561_, 0);
lean_dec(v_unused_4570_);
v___x_4563_ = v___x_4561_;
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
else
{
lean_dec(v___x_4561_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v_____s_4515_);
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_____s_4515_);
v___x_4566_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; 
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
}
}
else
{
lean_object* v___x_4571_; 
lean_dec(v___x_4561_);
v___x_4571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_4512_, v_fst_4521_);
if (lean_obj_tag(v___x_4571_) == 1)
{
lean_object* v_val_4572_; 
v_val_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_val_4572_);
lean_dec_ref_known(v___x_4571_, 1);
v_userName_4526_ = v_val_4572_;
v___y_4527_ = v___y_4518_;
goto v___jp_4525_;
}
else
{
lean_dec(v___x_4571_);
if (v_includeUnnamed_4513_ == 0)
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_del_object(v___x_4523_);
lean_dec(v_fst_4521_);
lean_dec(v___x_4510_);
lean_dec_ref(v_env_4509_);
v___x_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4573_, 0, v_____s_4515_);
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
return v___x_4574_;
}
else
{
lean_object* v___x_4575_; 
lean_inc(v_fst_4521_);
v___x_4575_ = l_Lean_Name_toString(v_fst_4521_, v_includeUnnamed_4513_);
v_userName_4526_ = v___x_4575_;
v___y_4527_ = v___y_4518_;
goto v___jp_4525_;
}
}
}
v___jp_4525_:
{
lean_object* v_ref_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v_ref_4528_ = lean_ctor_get(v___y_4527_, 2);
v___x_4529_ = 1;
v___x_4530_ = l_Lean_Options_empty;
v___x_4531_ = lean_box(0);
lean_inc(v_fst_4521_);
lean_inc_ref(v_env_4509_);
v___x_4532_ = l_Lean_findDocString_x3f(v_env_4509_, v_fst_4521_, v___x_4529_, v___x_4530_, v___x_4510_, v___x_4531_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4546_; 
lean_del_object(v___x_4523_);
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4546_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4546_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4537_ = l_Lean_NameSet_empty;
v___x_4538_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_4511_, v_fst_4521_, v___x_4537_);
lean_inc(v_fst_4521_);
v___x_4539_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_4509_, v_fst_4521_);
v___x_4540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4540_, 0, v_fst_4521_);
lean_ctor_set(v___x_4540_, 1, v_userName_4526_);
lean_ctor_set(v___x_4540_, 2, v___x_4538_);
lean_ctor_set(v___x_4540_, 3, v_a_4533_);
lean_ctor_set(v___x_4540_, 4, v___x_4539_);
v___x_4541_ = lean_array_push(v_____s_4515_, v___x_4540_);
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 0, v___x_4542_);
v___x_4544_ = v___x_4535_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v_userName_4526_);
lean_dec(v_fst_4521_);
lean_dec_ref(v_____s_4515_);
lean_dec_ref(v_env_4509_);
v_a_4547_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4549_ = v___x_4532_;
v_isShared_4550_ = v_isSharedCheck_4560_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4532_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4560_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4555_; 
v___x_4551_ = lean_io_error_to_string(v_a_4547_);
v___x_4552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
v___x_4553_ = l_Lean_MessageData_ofFormat(v___x_4552_);
lean_inc(v_ref_4528_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 1, v___x_4553_);
lean_ctor_set(v___x_4523_, 0, v_ref_4528_);
v___x_4555_ = v___x_4523_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_ref_4528_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v___x_4553_);
v___x_4555_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4557_; 
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4555_);
v___x_4557_ = v___x_4549_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_4578_, lean_object* v___x_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_includeUnnamed_4582_, lean_object* v_x_4583_, lean_object* v_____s_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
uint8_t v_includeUnnamed_boxed_4590_; lean_object* v_res_4591_; 
v_includeUnnamed_boxed_4590_ = lean_unbox(v_includeUnnamed_4582_);
v_res_4591_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4578_, v___x_4579_, v_a_4580_, v_a_4581_, v_includeUnnamed_boxed_4590_, v_x_4583_, v_____s_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v_a_4581_);
lean_dec(v_a_4580_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_4592_, size_t v_sz_4593_, size_t v_i_4594_, lean_object* v_b_4595_){
_start:
{
uint8_t v___x_4597_; 
v___x_4597_ = lean_usize_dec_lt(v_i_4594_, v_sz_4593_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_b_4595_);
return v___x_4598_;
}
else
{
lean_object* v_a_4599_; lean_object* v_fst_4600_; lean_object* v_snd_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; size_t v___x_4606_; size_t v___x_4607_; 
v_a_4599_ = lean_array_uget_borrowed(v_as_4592_, v_i_4594_);
v_fst_4600_ = lean_ctor_get(v_a_4599_, 0);
v_snd_4601_ = lean_ctor_get(v_a_4599_, 1);
v___x_4602_ = l_Lean_NameSet_empty;
v___x_4603_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4595_, v_fst_4600_, v___x_4602_);
lean_inc(v_snd_4601_);
v___x_4604_ = l_Lean_NameSet_insert(v___x_4603_, v_snd_4601_);
lean_inc(v_fst_4600_);
v___x_4605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4600_, v___x_4604_, v_b_4595_);
v___x_4606_ = ((size_t)1ULL);
v___x_4607_ = lean_usize_add(v_i_4594_, v___x_4606_);
v_i_4594_ = v___x_4607_;
v_b_4595_ = v___x_4605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_4609_, lean_object* v_sz_4610_, lean_object* v_i_4611_, lean_object* v_b_4612_, lean_object* v___y_4613_){
_start:
{
size_t v_sz_boxed_4614_; size_t v_i_boxed_4615_; lean_object* v_res_4616_; 
v_sz_boxed_4614_ = lean_unbox_usize(v_sz_4610_);
lean_dec(v_sz_4610_);
v_i_boxed_4615_ = lean_unbox_usize(v_i_4611_);
lean_dec(v_i_4611_);
v_res_4616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4609_, v_sz_boxed_4614_, v_i_boxed_4615_, v_b_4612_);
lean_dec_ref(v_as_4609_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_4617_, size_t v_sz_4618_, size_t v_i_4619_, lean_object* v_b_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
uint8_t v___x_4626_; 
v___x_4626_ = lean_usize_dec_lt(v_i_4619_, v_sz_4618_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; 
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_b_4620_);
return v___x_4627_;
}
else
{
lean_object* v_a_4628_; size_t v_sz_4629_; size_t v___x_4630_; lean_object* v___x_4631_; 
v_a_4628_ = lean_array_uget_borrowed(v_as_4617_, v_i_4619_);
v_sz_4629_ = lean_array_size(v_a_4628_);
v___x_4630_ = ((size_t)0ULL);
v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_4628_, v_sz_4629_, v___x_4630_, v_b_4620_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; size_t v___x_4633_; size_t v___x_4634_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref_known(v___x_4631_, 1);
v___x_4633_ = ((size_t)1ULL);
v___x_4634_ = lean_usize_add(v_i_4619_, v___x_4633_);
v_i_4619_ = v___x_4634_;
v_b_4620_ = v_a_4632_;
goto _start;
}
else
{
return v___x_4631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_4636_, lean_object* v_sz_4637_, lean_object* v_i_4638_, lean_object* v_b_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
size_t v_sz_boxed_4645_; size_t v_i_boxed_4646_; lean_object* v_res_4647_; 
v_sz_boxed_4645_ = lean_unbox_usize(v_sz_4637_);
lean_dec(v_sz_4637_);
v_i_boxed_4646_ = lean_unbox_usize(v_i_4638_);
lean_dec(v_i_4638_);
v_res_4647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4636_, v_sz_boxed_4645_, v_i_boxed_4646_, v_b_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec_ref(v_as_4636_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_4648_, lean_object* v_keys_4649_, lean_object* v_vals_4650_, lean_object* v_i_4651_, lean_object* v_acc_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4658_ = lean_array_get_size(v_keys_4649_);
v___x_4659_ = lean_nat_dec_lt(v_i_4651_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
lean_dec(v_i_4651_);
lean_dec_ref(v_f_4648_);
v___x_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4660_, 0, v_acc_4652_);
v___x_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
return v___x_4661_;
}
else
{
lean_object* v_k_4662_; lean_object* v_v_4663_; lean_object* v___x_4664_; 
v_k_4662_ = lean_array_fget_borrowed(v_keys_4649_, v_i_4651_);
v_v_4663_ = lean_array_fget_borrowed(v_vals_4650_, v_i_4651_);
lean_inc_ref(v_f_4648_);
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
lean_inc(v___y_4654_);
lean_inc_ref(v___y_4653_);
lean_inc(v_v_4663_);
lean_inc(v_k_4662_);
v___x_4664_ = lean_apply_8(v_f_4648_, v_acc_4652_, v_k_4662_, v_v_4663_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, lean_box(0));
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
if (lean_obj_tag(v_a_4665_) == 0)
{
lean_dec_ref_known(v_a_4665_, 1);
lean_dec(v_i_4651_);
lean_dec_ref(v_f_4648_);
return v___x_4664_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
lean_dec_ref_known(v___x_4664_, 1);
v_a_4666_ = lean_ctor_get(v_a_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v_a_4665_, 1);
v___x_4667_ = lean_unsigned_to_nat(1u);
v___x_4668_ = lean_nat_add(v_i_4651_, v___x_4667_);
lean_dec(v_i_4651_);
v_i_4651_ = v___x_4668_;
v_acc_4652_ = v_a_4666_;
goto _start;
}
}
else
{
lean_dec(v_i_4651_);
lean_dec_ref(v_f_4648_);
return v___x_4664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_4670_, lean_object* v_keys_4671_, lean_object* v_vals_4672_, lean_object* v_i_4673_, lean_object* v_acc_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4670_, v_keys_4671_, v_vals_4672_, v_i_4673_, v_acc_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec_ref(v_vals_4672_);
lean_dec_ref(v_keys_4671_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_4681_, lean_object* v_as_4682_, size_t v_i_4683_, size_t v_stop_4684_, lean_object* v_b_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_a_4692_; lean_object* v___y_4697_; uint8_t v___x_4700_; 
v___x_4700_ = lean_usize_dec_eq(v_i_4683_, v_stop_4684_);
if (v___x_4700_ == 0)
{
lean_object* v___x_4701_; 
v___x_4701_ = lean_array_uget_borrowed(v_as_4682_, v_i_4683_);
switch(lean_obj_tag(v___x_4701_))
{
case 0:
{
lean_object* v_key_4702_; lean_object* v_val_4703_; lean_object* v___x_4704_; 
v_key_4702_ = lean_ctor_get(v___x_4701_, 0);
v_val_4703_ = lean_ctor_get(v___x_4701_, 1);
lean_inc_ref(v_f_4681_);
lean_inc(v___y_4689_);
lean_inc_ref(v___y_4688_);
lean_inc(v___y_4687_);
lean_inc_ref(v___y_4686_);
lean_inc(v_val_4703_);
lean_inc(v_key_4702_);
v___x_4704_ = lean_apply_8(v_f_4681_, v_b_4685_, v_key_4702_, v_val_4703_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, lean_box(0));
v___y_4697_ = v___x_4704_;
goto v___jp_4696_;
}
case 1:
{
lean_object* v_node_4705_; lean_object* v___x_4706_; 
v_node_4705_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_node_4705_);
lean_inc_ref(v_f_4681_);
v___x_4706_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4681_, v_node_4705_, v_b_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
v___y_4697_ = v___x_4706_;
goto v___jp_4696_;
}
default: 
{
v_a_4692_ = v_b_4685_;
goto v___jp_4691_;
}
}
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
lean_dec_ref(v_f_4681_);
v___x_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4707_, 0, v_b_4685_);
v___x_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
return v___x_4708_;
}
v___jp_4691_:
{
size_t v___x_4693_; size_t v___x_4694_; 
v___x_4693_ = ((size_t)1ULL);
v___x_4694_ = lean_usize_add(v_i_4683_, v___x_4693_);
v_i_4683_ = v___x_4694_;
v_b_4685_ = v_a_4692_;
goto _start;
}
v___jp_4696_:
{
if (lean_obj_tag(v___y_4697_) == 0)
{
lean_object* v_a_4698_; 
v_a_4698_ = lean_ctor_get(v___y_4697_, 0);
if (lean_obj_tag(v_a_4698_) == 0)
{
lean_dec_ref(v_f_4681_);
return v___y_4697_;
}
else
{
lean_object* v_a_4699_; 
lean_inc_ref(v_a_4698_);
lean_dec_ref_known(v___y_4697_, 1);
v_a_4699_ = lean_ctor_get(v_a_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v_a_4698_, 1);
v_a_4692_ = v_a_4699_;
goto v___jp_4691_;
}
}
else
{
lean_dec_ref(v_f_4681_);
return v___y_4697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_4709_, lean_object* v_x_4710_, lean_object* v_x_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
if (lean_obj_tag(v_x_4710_) == 0)
{
lean_object* v_es_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4731_; 
v_es_4717_ = lean_ctor_get(v_x_4710_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_x_4710_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4719_ = v_x_4710_;
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_es_4717_);
lean_dec(v_x_4710_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4721_ = lean_unsigned_to_nat(0u);
v___x_4722_ = lean_array_get_size(v_es_4717_);
v___x_4723_ = lean_nat_dec_lt(v___x_4721_, v___x_4722_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4725_; 
lean_dec_ref(v_es_4717_);
lean_dec_ref(v_f_4709_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set_tag(v___x_4719_, 1);
lean_ctor_set(v___x_4719_, 0, v_x_4711_);
v___x_4725_ = v___x_4719_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_x_4711_);
v___x_4725_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; 
v___x_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
return v___x_4726_;
}
}
else
{
size_t v___x_4728_; size_t v___x_4729_; lean_object* v___x_4730_; 
lean_del_object(v___x_4719_);
v___x_4728_ = ((size_t)0ULL);
v___x_4729_ = lean_usize_of_nat(v___x_4722_);
v___x_4730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4709_, v_es_4717_, v___x_4728_, v___x_4729_, v_x_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec_ref(v_es_4717_);
return v___x_4730_;
}
}
}
else
{
lean_object* v_ks_4732_; lean_object* v_vs_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v_ks_4732_ = lean_ctor_get(v_x_4710_, 0);
lean_inc_ref(v_ks_4732_);
v_vs_4733_ = lean_ctor_get(v_x_4710_, 1);
lean_inc_ref(v_vs_4733_);
lean_dec_ref_known(v_x_4710_, 2);
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4709_, v_ks_4732_, v_vs_4733_, v___x_4734_, v_x_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec_ref(v_vs_4733_);
lean_dec_ref(v_ks_4732_);
return v___x_4735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_4736_, lean_object* v_x_4737_, lean_object* v_x_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4736_, v_x_4737_, v_x_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_4745_, lean_object* v_as_4746_, lean_object* v_i_4747_, lean_object* v_stop_4748_, lean_object* v_b_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
size_t v_i_boxed_4755_; size_t v_stop_boxed_4756_; lean_object* v_res_4757_; 
v_i_boxed_4755_ = lean_unbox_usize(v_i_4747_);
lean_dec(v_i_4747_);
v_stop_boxed_4756_ = lean_unbox_usize(v_stop_4748_);
lean_dec(v_stop_4748_);
v_res_4757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4745_, v_as_4746_, v_i_boxed_4755_, v_stop_boxed_4756_, v_b_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
lean_dec(v___y_4751_);
lean_dec_ref(v___y_4750_);
lean_dec_ref(v_as_4746_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_4758_, lean_object* v_s_4759_, lean_object* v_a_4760_, lean_object* v_b_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4767_, 0, v_a_4760_);
lean_ctor_set(v___x_4767_, 1, v_b_4761_);
lean_inc(v___y_4765_);
lean_inc_ref(v___y_4764_);
lean_inc(v___y_4763_);
lean_inc_ref(v___y_4762_);
v___x_4768_ = lean_apply_7(v_f_4758_, v___x_4767_, v_s_4759_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, lean_box(0));
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4795_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4771_ = v___x_4768_;
v_isShared_4772_ = v_isSharedCheck_4795_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4768_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4795_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
if (lean_obj_tag(v_a_4769_) == 0)
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4783_; 
v_a_4773_ = lean_ctor_get(v_a_4769_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_a_4769_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4775_ = v_a_4769_;
v_isShared_4776_ = v_isSharedCheck_4783_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v_a_4769_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4783_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
lean_object* v___x_4780_; 
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v___x_4778_);
v___x_4780_ = v___x_4771_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4794_; 
v_a_4784_ = lean_ctor_get(v_a_4769_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_a_4769_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4786_ = v_a_4769_;
v_isShared_4787_ = v_isSharedCheck_4794_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v_a_4769_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4794_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4791_; 
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v___x_4789_);
v___x_4791_ = v___x_4771_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
v_a_4796_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v___x_4768_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4768_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_4804_, lean_object* v_s_4805_, lean_object* v_a_4806_, lean_object* v_b_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_4804_, v_s_4805_, v_a_4806_, v_b_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_4814_, lean_object* v_init_4815_, lean_object* v_f_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v___f_4822_; lean_object* v___x_4823_; 
v___f_4822_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4822_, 0, v_f_4816_);
lean_inc_ref(v_map_4814_);
v___x_4823_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_4822_, v_map_4814_, v_init_4815_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4832_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4826_ = v___x_4823_;
v_isShared_4827_ = v_isSharedCheck_4832_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4823_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4832_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v_a_4828_; lean_object* v___x_4830_; 
v_a_4828_ = lean_ctor_get(v_a_4824_, 0);
lean_inc(v_a_4828_);
lean_dec(v_a_4824_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v_a_4828_);
v___x_4830_ = v___x_4826_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4828_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_a_4833_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4823_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4823_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_4841_, lean_object* v_init_4842_, lean_object* v_f_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4841_, v_init_4842_, v_f_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec_ref(v_map_4841_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v_env_4856_; lean_object* v___x_4857_; lean_object* v_ext_4858_; lean_object* v_toEnvExtension_4859_; lean_object* v_asyncMode_4860_; uint8_t v___x_4861_; lean_object* v___x_4862_; lean_object* v_categories_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4852_ = lean_box(1);
v___x_4853_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4854_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4855_ = lean_st_ref_get(v___y_4850_);
v_env_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc_ref_n(v_env_4856_, 2);
lean_dec(v___x_4855_);
v___x_4857_ = l_Lean_Parser_parserExtension;
v_ext_4858_ = lean_ctor_get(v___x_4857_, 1);
v_toEnvExtension_4859_ = lean_ctor_get(v_ext_4858_, 0);
v_asyncMode_4860_ = lean_ctor_get(v_toEnvExtension_4859_, 2);
v___x_4861_ = 0;
v___x_4862_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4854_, v___x_4857_, v_env_4856_, v_asyncMode_4860_, v___x_4861_);
v_categories_4863_ = lean_ctor_get(v___x_4862_, 2);
lean_inc_ref(v_categories_4863_);
lean_dec(v___x_4862_);
v___x_4864_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4863_, v___x_4864_);
lean_dec_ref(v_categories_4863_);
if (lean_obj_tag(v___x_4865_) == 1)
{
lean_object* v_val_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4897_; 
v_val_4866_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4868_ = v___x_4865_;
v_isShared_4869_ = v_isSharedCheck_4897_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_val_4866_);
lean_dec(v___x_4865_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4897_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___y_4871_; lean_object* v___x_4880_; lean_object* v_toEnvExtension_4881_; lean_object* v_exportEntriesFn_4882_; lean_object* v_asyncMode_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v_importedEntries_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v_exported_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4880_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4881_ = lean_ctor_get(v___x_4880_, 0);
v_exportEntriesFn_4882_ = lean_ctor_get(v___x_4880_, 4);
v_asyncMode_4883_ = lean_ctor_get(v_toEnvExtension_4881_, 2);
v___x_4884_ = lean_box(0);
lean_inc_ref_n(v_env_4856_, 2);
v___x_4885_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4853_, v_toEnvExtension_4881_, v_env_4856_, v_asyncMode_4883_, v___x_4884_, v___x_4861_);
v_importedEntries_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc_ref(v_importedEntries_4886_);
lean_dec(v___x_4885_);
v___x_4887_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4852_, v___x_4880_, v_env_4856_, v_asyncMode_4883_, v___x_4884_, v___x_4861_);
lean_inc_ref(v_exportEntriesFn_4882_);
v___x_4888_ = lean_apply_2(v_exportEntriesFn_4882_, v_env_4856_, v___x_4887_);
v_exported_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_exported_4889_);
lean_dec_ref(v___x_4888_);
v___x_4890_ = lean_array_push(v_importedEntries_4886_, v_exported_4889_);
v___x_4891_ = lean_unsigned_to_nat(0u);
v___x_4892_ = lean_array_get_size(v___x_4890_);
v___x_4893_ = lean_nat_dec_lt(v___x_4891_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_dec_ref(v___x_4890_);
v___y_4871_ = v___x_4852_;
goto v___jp_4870_;
}
else
{
size_t v___x_4894_; size_t v___x_4895_; lean_object* v___x_4896_; 
v___x_4894_ = ((size_t)0ULL);
v___x_4895_ = lean_usize_of_nat(v___x_4892_);
v___x_4896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4890_, v___x_4894_, v___x_4895_, v___x_4852_);
lean_dec_ref(v___x_4890_);
v___y_4871_ = v___x_4896_;
goto v___jp_4870_;
}
v___jp_4870_:
{
lean_object* v_tables_4872_; lean_object* v_leadingTable_4873_; lean_object* v_trailingTable_4874_; lean_object* v_firstTokens_4875_; lean_object* v_firstTokens_4876_; lean_object* v___x_4878_; 
v_tables_4872_ = lean_ctor_get(v_val_4866_, 2);
v_leadingTable_4873_ = lean_ctor_get(v_tables_4872_, 0);
v_trailingTable_4874_ = lean_ctor_get(v_tables_4872_, 2);
lean_inc(v_trailingTable_4874_);
lean_inc(v_leadingTable_4873_);
lean_inc(v_val_4866_);
v_firstTokens_4875_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4866_, v_leadingTable_4873_, v___y_4871_);
v_firstTokens_4876_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4866_, v_trailingTable_4874_, v_firstTokens_4875_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set_tag(v___x_4868_, 0);
lean_ctor_set(v___x_4868_, 0, v_firstTokens_4876_);
v___x_4878_ = v___x_4868_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_firstTokens_4876_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
else
{
lean_object* v___x_4898_; 
lean_dec(v___x_4865_);
lean_dec_ref(v_env_4856_);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4852_);
return v___x_4898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4899_);
lean_dec(v___y_4899_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v_env_4914_; lean_object* v___x_4915_; lean_object* v_toEnvExtension_4916_; lean_object* v_exportEntriesFn_4917_; lean_object* v_asyncMode_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v_importedEntries_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v_exported_4925_; lean_object* v___x_4926_; size_t v_sz_4927_; size_t v___x_4928_; lean_object* v___x_4929_; 
v___x_4910_ = lean_box(1);
v___x_4911_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4912_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4913_ = lean_st_ref_get(v_a_4908_);
v_env_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc_ref_n(v_env_4914_, 4);
lean_dec(v___x_4913_);
v___x_4915_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4916_ = lean_ctor_get(v___x_4915_, 0);
v_exportEntriesFn_4917_ = lean_ctor_get(v___x_4915_, 4);
v_asyncMode_4918_ = lean_ctor_get(v_toEnvExtension_4916_, 2);
v___x_4919_ = lean_box(0);
v___x_4920_ = 0;
v___x_4921_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4911_, v_toEnvExtension_4916_, v_env_4914_, v_asyncMode_4918_, v___x_4919_, v___x_4920_);
v_importedEntries_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc_ref(v_importedEntries_4922_);
lean_dec(v___x_4921_);
v___x_4923_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4910_, v___x_4915_, v_env_4914_, v_asyncMode_4918_, v___x_4919_, v___x_4920_);
lean_inc_ref(v_exportEntriesFn_4917_);
v___x_4924_ = lean_apply_2(v_exportEntriesFn_4917_, v_env_4914_, v___x_4923_);
v_exported_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc(v_exported_4925_);
lean_dec_ref(v___x_4924_);
v___x_4926_ = lean_array_push(v_importedEntries_4922_, v_exported_4925_);
v_sz_4927_ = lean_array_size(v___x_4926_);
v___x_4928_ = ((size_t)0ULL);
v___x_4929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_4926_, v_sz_4927_, v___x_4928_, v___x_4910_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
lean_dec_ref(v___x_4926_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4953_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4953_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4953_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v_ext_4935_; lean_object* v_toEnvExtension_4936_; lean_object* v_asyncMode_4937_; lean_object* v___x_4938_; lean_object* v_categories_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4934_ = l_Lean_Parser_parserExtension;
v_ext_4935_ = lean_ctor_get(v___x_4934_, 1);
v_toEnvExtension_4936_ = lean_ctor_get(v_ext_4935_, 0);
v_asyncMode_4937_ = lean_ctor_get(v_toEnvExtension_4936_, 2);
lean_inc_ref(v_env_4914_);
v___x_4938_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4912_, v___x_4934_, v_env_4914_, v_asyncMode_4937_, v___x_4920_);
v_categories_4939_ = lean_ctor_get(v___x_4938_, 2);
lean_inc_ref(v_categories_4939_);
lean_dec(v___x_4938_);
v___x_4940_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_4941_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4942_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4939_, v___x_4941_);
lean_dec_ref(v_categories_4939_);
if (lean_obj_tag(v___x_4942_) == 1)
{
lean_object* v_val_4943_; lean_object* v___x_4944_; lean_object* v_a_4945_; lean_object* v_kinds_4946_; lean_object* v___x_4947_; lean_object* v___f_4948_; lean_object* v___x_4949_; 
lean_del_object(v___x_4932_);
v_val_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_val_4943_);
lean_dec_ref_known(v___x_4942_, 1);
v___x_4944_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_4908_);
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref(v___x_4944_);
v_kinds_4946_ = lean_ctor_get(v_val_4943_, 1);
lean_inc_ref(v_kinds_4946_);
lean_dec(v_val_4943_);
v___x_4947_ = lean_box(v_includeUnnamed_4904_);
v___f_4948_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4948_, 0, v_env_4914_);
lean_closure_set(v___f_4948_, 1, v___x_4919_);
lean_closure_set(v___f_4948_, 2, v_a_4930_);
lean_closure_set(v___f_4948_, 3, v_a_4945_);
lean_closure_set(v___f_4948_, 4, v___x_4947_);
v___x_4949_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_4946_, v___x_4940_, v___f_4948_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
lean_dec_ref(v_kinds_4946_);
return v___x_4949_;
}
else
{
lean_object* v___x_4951_; 
lean_dec(v___x_4942_);
lean_dec(v_a_4930_);
lean_dec_ref(v_env_4914_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4940_);
v___x_4951_ = v___x_4932_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4940_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec_ref(v_env_4914_);
v_a_4954_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4929_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4929_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
uint8_t v_includeUnnamed_boxed_4968_; lean_object* v_res_4969_; 
v_includeUnnamed_boxed_4968_ = lean_unbox(v_includeUnnamed_4962_);
v_res_4969_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_4968_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
lean_dec(v_a_4966_);
lean_dec_ref(v_a_4965_);
lean_dec(v_a_4964_);
lean_dec_ref(v_a_4963_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_4970_, size_t v_sz_4971_, size_t v_i_4972_, lean_object* v_b_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4970_, v_sz_4971_, v_i_4972_, v_b_4973_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_4980_, lean_object* v_sz_4981_, lean_object* v_i_4982_, lean_object* v_b_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
size_t v_sz_boxed_4989_; size_t v_i_boxed_4990_; lean_object* v_res_4991_; 
v_sz_boxed_4989_ = lean_unbox_usize(v_sz_4981_);
lean_dec(v_sz_4981_);
v_i_boxed_4990_ = lean_unbox_usize(v_i_4982_);
lean_dec(v_i_4982_);
v_res_4991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_4980_, v_sz_boxed_4989_, v_i_boxed_4990_, v_b_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
lean_dec(v___y_4987_);
lean_dec_ref(v___y_4986_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec_ref(v_as_4980_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_5004_, lean_object* v_00_u03b2_5005_, lean_object* v_map_5006_, lean_object* v_init_5007_, lean_object* v_f_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v___x_5014_; 
v___x_5014_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_5006_, v_init_5007_, v_f_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_5015_, lean_object* v_00_u03b2_5016_, lean_object* v_map_5017_, lean_object* v_init_5018_, lean_object* v_f_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_5015_, v_00_u03b2_5016_, v_map_5017_, v_init_5018_, v_f_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec_ref(v_map_5017_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_5026_, lean_object* v_f_5027_, lean_object* v_init_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5027_, v_map_5026_, v_init_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_5035_, lean_object* v_f_5036_, lean_object* v_init_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_5035_, v_f_5036_, v_init_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
return v_res_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_5044_, lean_object* v_00_u03c3_5045_, lean_object* v_00_u03b2_5046_, lean_object* v_map_5047_, lean_object* v_f_5048_, lean_object* v_init_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5048_, v_map_5047_, v_init_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_5056_, lean_object* v_00_u03c3_5057_, lean_object* v_00_u03b2_5058_, lean_object* v_map_5059_, lean_object* v_f_5060_, lean_object* v_init_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_5056_, v_00_u03c3_5057_, v_00_u03b2_5058_, v_map_5059_, v_f_5060_, v_init_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_5068_, lean_object* v_00_u03c3_5069_, lean_object* v_00_u03b1_5070_, lean_object* v_00_u03b2_5071_, lean_object* v_f_5072_, lean_object* v_x_5073_, lean_object* v_x_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5072_, v_x_5073_, v_x_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_5081_, lean_object* v_00_u03c3_5082_, lean_object* v_00_u03b1_5083_, lean_object* v_00_u03b2_5084_, lean_object* v_f_5085_, lean_object* v_x_5086_, lean_object* v_x_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_5081_, v_00_u03c3_5082_, v_00_u03b1_5083_, v_00_u03b2_5084_, v_f_5085_, v_x_5086_, v_x_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_5094_, lean_object* v_00_u03b2_5095_, lean_object* v_00_u03c3_5096_, lean_object* v_00_u03c3_5097_, lean_object* v_f_5098_, lean_object* v_as_5099_, size_t v_i_5100_, size_t v_stop_5101_, lean_object* v_b_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v___x_5108_; 
v___x_5108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5098_, v_as_5099_, v_i_5100_, v_stop_5101_, v_b_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5109_, lean_object* v_00_u03b2_5110_, lean_object* v_00_u03c3_5111_, lean_object* v_00_u03c3_5112_, lean_object* v_f_5113_, lean_object* v_as_5114_, lean_object* v_i_5115_, lean_object* v_stop_5116_, lean_object* v_b_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
size_t v_i_boxed_5123_; size_t v_stop_boxed_5124_; lean_object* v_res_5125_; 
v_i_boxed_5123_ = lean_unbox_usize(v_i_5115_);
lean_dec(v_i_5115_);
v_stop_boxed_5124_ = lean_unbox_usize(v_stop_5116_);
lean_dec(v_stop_5116_);
v_res_5125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_5109_, v_00_u03b2_5110_, v_00_u03c3_5111_, v_00_u03c3_5112_, v_f_5113_, v_as_5114_, v_i_boxed_5123_, v_stop_boxed_5124_, v_b_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec_ref(v_as_5114_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_5126_, lean_object* v_00_u03c3_5127_, lean_object* v_00_u03b1_5128_, lean_object* v_00_u03b2_5129_, lean_object* v_f_5130_, lean_object* v_keys_5131_, lean_object* v_vals_5132_, lean_object* v_heq_5133_, lean_object* v_i_5134_, lean_object* v_acc_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_5130_, v_keys_5131_, v_vals_5132_, v_i_5134_, v_acc_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_5142_, lean_object* v_00_u03c3_5143_, lean_object* v_00_u03b1_5144_, lean_object* v_00_u03b2_5145_, lean_object* v_f_5146_, lean_object* v_keys_5147_, lean_object* v_vals_5148_, lean_object* v_heq_5149_, lean_object* v_i_5150_, lean_object* v_acc_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_5142_, v_00_u03c3_5143_, v_00_u03b1_5144_, v_00_u03b2_5145_, v_f_5146_, v_keys_5147_, v_vals_5148_, v_heq_5149_, v_i_5150_, v_acc_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec_ref(v_vals_5148_);
lean_dec_ref(v_keys_5147_);
return v_res_5157_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
