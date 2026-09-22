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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed 'register_tactic_tag' command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
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
size_t v_sz_boxed_53_; size_t v___x_6039__boxed_54_; lean_object* v_res_55_; 
v_sz_boxed_53_ = lean_unbox_usize(v_sz_46_);
lean_dec(v_sz_46_);
v___x_6039__boxed_54_ = lean_unbox_usize(v___x_47_);
lean_dec(v___x_47_);
v_res_55_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(v_x_45_, v_sz_boxed_53_, v___x_6039__boxed_54_, v_content_48_, v___y_49_, v___y_50_, v___y_51_);
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
size_t v_sz_boxed_625_; size_t v___x_6901__boxed_626_; lean_object* v_res_627_; 
v_sz_boxed_625_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v___x_6901__boxed_626_ = lean_unbox_usize(v___x_619_);
lean_dec(v___x_619_);
v_res_627_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(v_sz_boxed_625_, v___x_6901__boxed_626_, v_content_620_, v___y_621_, v___y_622_, v___y_623_);
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
lean_object* v___x_1225_; lean_object* v_env_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_scopes_1229_; lean_object* v___x_1230_; lean_object* v_opts_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1225_ = lean_st_ref_get(v___y_1223_);
v_env_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_ref(v_env_1226_);
lean_dec(v___x_1225_);
v___x_1227_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1228_ = lean_st_ref_get(v___y_1223_);
v_scopes_1229_ = lean_ctor_get(v___x_1228_, 2);
lean_inc(v_scopes_1229_);
lean_dec(v___x_1228_);
v___x_1230_ = l_List_head_x21___redArg(v___x_1227_, v_scopes_1229_);
lean_dec(v_scopes_1229_);
v_opts_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc_ref(v_opts_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2);
v___x_1233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5);
v___x_1234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1234_, 0, v_env_1226_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
lean_ctor_set(v___x_1234_, 3, v_opts_1231_);
v___x_1235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_msgData_1222_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_msgData_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1237_, v___y_1238_);
lean_dec(v___y_1238_);
return v_res_1240_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(1);
v___x_1242_ = l_Lean_MessageData_ofFormat(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2));
v___x_1247_ = l_Lean_MessageData_ofFormat(v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
return v_x_1248_;
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1273_; 
v_head_1250_ = lean_ctor_get(v_x_1249_, 0);
v_tail_1251_ = lean_ctor_get(v_x_1249_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1249_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1253_ = v_x_1249_;
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_tail_1251_);
lean_inc(v_head_1250_);
lean_dec(v_x_1249_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_before_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1271_; 
v_before_1255_ = lean_ctor_get(v_head_1250_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_head_1250_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_head_1250_, 1);
lean_dec(v_unused_1272_);
v___x_1257_ = v_head_1250_;
v_isShared_1258_ = v_isSharedCheck_1271_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_before_1255_);
lean_dec(v_head_1250_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1271_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 7);
lean_ctor_set(v___x_1257_, 1, v___x_1259_);
lean_ctor_set(v___x_1257_, 0, v_x_1248_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_x_1248_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 7);
lean_ctor_set(v___x_1253_, 1, v___x_1262_);
lean_ctor_set(v___x_1253_, 0, v___x_1261_);
v___x_1264_ = v___x_1253_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = l_Lean_MessageData_ofSyntax(v_before_1255_);
v___x_1266_ = l_Lean_indentD(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1264_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v_x_1248_ = v___x_1267_;
v_x_1249_ = v_tail_1251_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(lean_object* v_opts_1274_, lean_object* v_opt_1275_){
_start:
{
lean_object* v_name_1276_; lean_object* v_defValue_1277_; lean_object* v_map_1278_; lean_object* v___x_1279_; 
v_name_1276_ = lean_ctor_get(v_opt_1275_, 0);
v_defValue_1277_ = lean_ctor_get(v_opt_1275_, 1);
v_map_1278_ = lean_ctor_get(v_opts_1274_, 0);
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1278_, v_name_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_unbox(v_defValue_1277_);
return v___x_1280_;
}
else
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1279_, 1);
if (lean_obj_tag(v_val_1281_) == 1)
{
uint8_t v_v_1282_; 
v_v_1282_ = lean_ctor_get_uint8(v_val_1281_, 0);
lean_dec_ref_known(v_val_1281_, 0);
return v_v_1282_;
}
else
{
uint8_t v___x_1283_; 
lean_dec(v_val_1281_);
v___x_1283_ = lean_unbox(v_defValue_1277_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17___boxed(lean_object* v_opts_1284_, lean_object* v_opt_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1284_, v_opt_1285_);
lean_dec_ref(v_opt_1285_);
lean_dec_ref(v_opts_1284_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1));
v___x_1292_ = l_Lean_MessageData_ofFormat(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_msgData_1293_, lean_object* v_macroStack_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_scopes_1299_; lean_object* v___x_1300_; lean_object* v_opts_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1297_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1298_ = lean_st_ref_get(v___y_1295_);
v_scopes_1299_ = lean_ctor_get(v___x_1298_, 2);
lean_inc(v_scopes_1299_);
lean_dec(v___x_1298_);
v___x_1300_ = l_List_head_x21___redArg(v___x_1297_, v_scopes_1299_);
lean_dec(v_scopes_1299_);
v_opts_1301_ = lean_ctor_get(v___x_1300_, 1);
lean_inc_ref(v_opts_1301_);
lean_dec(v___x_1300_);
v___x_1302_ = l_Lean_Elab_pp_macroStack;
v___x_1303_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1301_, v___x_1302_);
lean_dec_ref(v_opts_1301_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_macroStack_1294_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_msgData_1293_);
return v___x_1304_;
}
else
{
if (lean_obj_tag(v_macroStack_1294_) == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_msgData_1293_);
return v___x_1305_;
}
else
{
lean_object* v_head_1306_; lean_object* v_after_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1322_; 
v_head_1306_ = lean_ctor_get(v_macroStack_1294_, 0);
lean_inc(v_head_1306_);
v_after_1307_ = lean_ctor_get(v_head_1306_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_head_1306_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_head_1306_, 0);
lean_dec(v_unused_1323_);
v___x_1309_ = v_head_1306_;
v_isShared_1310_ = v_isSharedCheck_1322_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_after_1307_);
lean_dec(v_head_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1322_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 7);
lean_ctor_set(v___x_1309_, 1, v___x_1311_);
lean_ctor_set(v___x_1309_, 0, v_msgData_1293_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_msgData_1293_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_msgData_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1314_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_MessageData_ofSyntax(v_after_1307_);
v___x_1317_ = l_Lean_indentD(v___x_1316_);
v_msgData_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1318_, 0, v___x_1315_);
lean_ctor_set(v_msgData_1318_, 1, v___x_1317_);
v___x_1319_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(v_msgData_1318_, v_macroStack_1294_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_msgData_1324_, lean_object* v_macroStack_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1324_, v_macroStack_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Elab_Command_getRef___redArg(v___y_1330_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_macroStack_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1348_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v_macroStack_1335_ = lean_ctor_get(v___y_1330_, 4);
v___x_1336_ = l_Lean_Elab_getBetterRef(v_a_1334_, v_macroStack_1335_);
lean_dec(v_a_1334_);
v___x_1337_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msg_1329_, v___y_1331_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
lean_inc(v_macroStack_1335_);
v___x_1339_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_a_1338_, v_macroStack_1335_, v___y_1331_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1336_);
lean_ctor_set(v___x_1344_, 1, v_a_1340_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 1);
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_msg_1329_);
v_a_1349_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1333_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1333_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object* v_ref_1362_, lean_object* v_msg_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Elab_Command_getRef___redArg(v___y_1364_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v_fileName_1369_; lean_object* v_fileMap_1370_; lean_object* v_currRecDepth_1371_; lean_object* v_cmdPos_1372_; lean_object* v_macroStack_1373_; lean_object* v_quotContext_x3f_1374_; lean_object* v_currMacroScope_1375_; lean_object* v_snap_x3f_1376_; lean_object* v_cancelTk_x3f_1377_; uint8_t v_suppressElabErrors_1378_; lean_object* v_ref_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v_fileName_1369_ = lean_ctor_get(v___y_1364_, 0);
v_fileMap_1370_ = lean_ctor_get(v___y_1364_, 1);
v_currRecDepth_1371_ = lean_ctor_get(v___y_1364_, 2);
v_cmdPos_1372_ = lean_ctor_get(v___y_1364_, 3);
v_macroStack_1373_ = lean_ctor_get(v___y_1364_, 4);
v_quotContext_x3f_1374_ = lean_ctor_get(v___y_1364_, 5);
v_currMacroScope_1375_ = lean_ctor_get(v___y_1364_, 6);
v_snap_x3f_1376_ = lean_ctor_get(v___y_1364_, 8);
v_cancelTk_x3f_1377_ = lean_ctor_get(v___y_1364_, 9);
v_suppressElabErrors_1378_ = lean_ctor_get_uint8(v___y_1364_, sizeof(void*)*10);
v_ref_1379_ = l_Lean_replaceRef(v_ref_1362_, v_a_1368_);
lean_dec(v_a_1368_);
lean_inc(v_cancelTk_x3f_1377_);
lean_inc(v_snap_x3f_1376_);
lean_inc(v_currMacroScope_1375_);
lean_inc(v_quotContext_x3f_1374_);
lean_inc(v_macroStack_1373_);
lean_inc(v_cmdPos_1372_);
lean_inc(v_currRecDepth_1371_);
lean_inc_ref(v_fileMap_1370_);
lean_inc_ref(v_fileName_1369_);
v___x_1380_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1380_, 0, v_fileName_1369_);
lean_ctor_set(v___x_1380_, 1, v_fileMap_1370_);
lean_ctor_set(v___x_1380_, 2, v_currRecDepth_1371_);
lean_ctor_set(v___x_1380_, 3, v_cmdPos_1372_);
lean_ctor_set(v___x_1380_, 4, v_macroStack_1373_);
lean_ctor_set(v___x_1380_, 5, v_quotContext_x3f_1374_);
lean_ctor_set(v___x_1380_, 6, v_currMacroScope_1375_);
lean_ctor_set(v___x_1380_, 7, v_ref_1379_);
lean_ctor_set(v___x_1380_, 8, v_snap_x3f_1376_);
lean_ctor_set(v___x_1380_, 9, v_cancelTk_x3f_1377_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*10, v_suppressElabErrors_1378_);
v___x_1381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1363_, v___x_1380_, v___y_1365_);
lean_dec_ref_known(v___x_1380_, 10);
return v___x_1381_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_msg_1363_);
v_a_1382_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1367_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1367_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object* v_ref_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1390_, v_msg_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_ref_1390_);
return v_res_1395_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object* v_stx_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1413_);
if (lean_obj_tag(v___x_1414_) == 1)
{
lean_object* v_kind_1415_; 
v_kind_1415_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_kind_1415_);
if (lean_obj_tag(v_kind_1415_) == 1)
{
lean_object* v_pre_1416_; 
v_pre_1416_ = lean_ctor_get(v_kind_1415_, 0);
lean_inc(v_pre_1416_);
if (lean_obj_tag(v_pre_1416_) == 1)
{
lean_object* v_pre_1417_; 
v_pre_1417_ = lean_ctor_get(v_pre_1416_, 0);
lean_inc(v_pre_1417_);
if (lean_obj_tag(v_pre_1417_) == 1)
{
lean_object* v_pre_1418_; 
v_pre_1418_ = lean_ctor_get(v_pre_1417_, 0);
lean_inc(v_pre_1418_);
if (lean_obj_tag(v_pre_1418_) == 1)
{
lean_object* v_pre_1419_; 
v_pre_1419_ = lean_ctor_get(v_pre_1418_, 0);
if (lean_obj_tag(v_pre_1419_) == 0)
{
lean_object* v_args_1420_; lean_object* v_str_1421_; lean_object* v_str_1422_; lean_object* v_str_1423_; lean_object* v_str_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_args_1420_ = lean_ctor_get(v___x_1414_, 2);
lean_inc_ref(v_args_1420_);
lean_dec_ref_known(v___x_1414_, 3);
v_str_1421_ = lean_ctor_get(v_kind_1415_, 1);
lean_inc_ref(v_str_1421_);
lean_dec_ref_known(v_kind_1415_, 2);
v_str_1422_ = lean_ctor_get(v_pre_1416_, 1);
lean_inc_ref(v_str_1422_);
lean_dec_ref_known(v_pre_1416_, 2);
v_str_1423_ = lean_ctor_get(v_pre_1417_, 1);
lean_inc_ref(v_str_1423_);
lean_dec_ref_known(v_pre_1417_, 2);
v_str_1424_ = lean_ctor_get(v_pre_1418_, 1);
lean_inc_ref(v_str_1424_);
lean_dec_ref_known(v_pre_1418_, 2);
v___x_1425_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2));
v___x_1426_ = lean_string_dec_eq(v_str_1424_, v___x_1425_);
lean_dec_ref(v_str_1424_);
if (v___x_1426_ == 0)
{
lean_dec_ref(v_str_1423_);
lean_dec_ref(v_str_1422_);
lean_dec_ref(v_str_1421_);
lean_dec_ref(v_args_1420_);
goto v___jp_1407_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3));
v___x_1428_ = lean_string_dec_eq(v_str_1423_, v___x_1427_);
lean_dec_ref(v_str_1423_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v_str_1422_);
lean_dec_ref(v_str_1421_);
lean_dec_ref(v_args_1420_);
goto v___jp_1407_;
}
else
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4));
v___x_1430_ = lean_string_dec_eq(v_str_1422_, v___x_1429_);
lean_dec_ref(v_str_1422_);
if (v___x_1430_ == 0)
{
lean_dec_ref(v_str_1421_);
lean_dec_ref(v_args_1420_);
goto v___jp_1407_;
}
else
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5));
v___x_1432_ = lean_string_dec_eq(v_str_1421_, v___x_1431_);
lean_dec_ref(v_str_1421_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v_args_1420_);
goto v___jp_1407_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_array_get_size(v_args_1420_);
v___x_1434_ = lean_unsigned_to_nat(2u);
v___x_1435_ = lean_nat_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec_ref(v_args_1420_);
goto v___jp_1407_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_array_fget(v_args_1420_, v___x_1436_);
lean_dec_ref(v_args_1420_);
if (lean_obj_tag(v___x_1437_) == 2)
{
lean_object* v_val_1438_; lean_object* v___x_1439_; 
lean_dec(v_stx_1403_);
v_val_1438_ = lean_ctor_get(v___x_1437_, 1);
lean_inc_ref(v_val_1438_);
lean_dec_ref_known(v___x_1437_, 2);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_val_1438_);
return v___x_1439_;
}
else
{
lean_dec(v___x_1437_);
goto v___jp_1407_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1418_, 2);
lean_dec_ref_known(v_pre_1417_, 2);
lean_dec_ref_known(v_pre_1416_, 2);
lean_dec_ref_known(v_kind_1415_, 2);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec_ref_known(v_pre_1417_, 2);
lean_dec(v_pre_1418_);
lean_dec_ref_known(v_pre_1416_, 2);
lean_dec_ref_known(v_kind_1415_, 2);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec(v_pre_1417_);
lean_dec_ref_known(v_pre_1416_, 2);
lean_dec_ref_known(v_kind_1415_, 2);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec_ref_known(v_kind_1415_, 2);
lean_dec(v_pre_1416_);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec(v_kind_1415_);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec(v___x_1414_);
goto v___jp_1407_;
}
v___jp_1407_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1408_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1);
lean_inc(v_stx_1403_);
v___x_1409_ = l_Lean_MessageData_ofSyntax(v_stx_1403_);
v___x_1410_ = l_Lean_indentD(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1408_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_stx_1403_, v___x_1411_, v___y_1404_, v___y_1405_);
lean_dec(v_stx_1403_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object* v_stx_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_stx_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object* v_doc_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Lean_isVersoDocComment(v_doc_1445_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_doc_1445_, v_a_1446_, v_a_1447_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___boxed), 4, 1);
lean_closure_set(v___x_1451_, 0, v_doc_1445_);
v___x_1452_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1451_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1483_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1483_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1483_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
if (lean_obj_tag(v_a_1453_) == 1)
{
lean_object* v_val_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_del_object(v___x_1455_);
v_val_1457_ = lean_ctor_get(v_a_1453_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v_a_1453_, 1);
v___x_1458_ = l_Lean_TSyntax_getVersoBlocks(v_val_1457_);
lean_dec(v_val_1457_);
v___x_1459_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1459_, 0, v___x_1458_);
v___x_1460_ = 0;
v___x_1461_ = lean_box(v___x_1460_);
v___x_1462_ = lean_alloc_closure((void*)(l_Lean_Doc_DocM_execForModule___boxed), 10, 3);
lean_closure_set(v___x_1462_, 0, lean_box(0));
lean_closure_set(v___x_1462_, 1, v___x_1459_);
lean_closure_set(v___x_1462_, 2, v___x_1461_);
v___x_1463_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1462_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v_fst_1465_; lean_object* v_fst_1466_; lean_object* v_snd_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v_fst_1465_ = lean_ctor_get(v_a_1464_, 0);
lean_inc(v_fst_1465_);
lean_dec(v_a_1464_);
v_fst_1466_ = lean_ctor_get(v_fst_1465_, 0);
lean_inc(v_fst_1466_);
v_snd_1467_ = lean_ctor_get(v_fst_1465_, 1);
lean_inc(v_snd_1467_);
lean_dec(v_fst_1465_);
v___f_1468_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1468_, 0, v_fst_1466_);
lean_closure_set(v___f_1468_, 1, v_snd_1467_);
v___x_1469_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_1469_, 0, v___f_1468_);
v___x_1470_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1469_, v_a_1446_, v_a_1447_);
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1463_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1463_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_dec(v_a_1453_);
v___x_1479_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1479_);
v___x_1481_ = v___x_1455_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1452_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1452_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object* v_doc_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_doc_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object* v_p_1497_, lean_object* v_level_1498_, lean_object* v_part_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1498_, v_part_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object* v_p_1505_, lean_object* v_level_1506_, lean_object* v_part_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(v_p_1505_, v_level_1506_, v_part_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec(v_level_1506_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object* v_00_u03b1_1513_, lean_object* v_ref_1514_, lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1514_, v_msg_1515_, v___y_1516_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_ref_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(v_00_u03b1_1520_, v_ref_1521_, v_msg_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v_ref_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(lean_object* v_p_1527_, lean_object* v___x_1528_, size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_bs_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1528_, v_sz_1529_, v_i_1530_, v_bs_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___boxed(lean_object* v_p_1537_, lean_object* v___x_1538_, lean_object* v_sz_1539_, lean_object* v_i_1540_, lean_object* v_bs_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1539_);
lean_dec(v_sz_1539_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1540_);
lean_dec(v_i_1540_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(v_p_1537_, v___x_1538_, v_sz_boxed_1546_, v_i_boxed_1547_, v_bs_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec(v___x_1538_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(lean_object* v_msgData_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1549_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(v_msgData_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1559_, lean_object* v_msg_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1560_, v___y_1561_, v___y_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(v_00_u03b1_1565_, v_msg_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(lean_object* v_msgData_1571_, lean_object* v_macroStack_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1571_, v_macroStack_1572_, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_msgData_1577_, lean_object* v_macroStack_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(v_msgData_1577_, v_macroStack_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1583_, v___x_1584_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(v___x_1593_, v___x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
lean_inc(v_x_1633_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v_x_1633_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v_x_1633_);
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1640_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1639_, v_a_1634_, v_a_1635_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = l_Lean_Syntax_getArg(v_x_1633_, v___x_1641_);
lean_inc(v___x_1642_);
v___x_1643_ = l_Lean_Syntax_matchesNull(v___x_1642_, v___x_1641_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1642_);
v___x_1645_ = l_Lean_Syntax_matchesNull(v___x_1642_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v___x_1642_);
lean_dec(v_x_1633_);
v___x_1646_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1647_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1646_, v_a_1634_, v_a_1635_);
return v___x_1647_;
}
else
{
lean_object* v_docs_1648_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; uint8_t v___y_1704_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1720_; 
v_docs_1648_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1641_);
lean_dec(v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_docs_1648_);
v___x_1754_ = l_Lean_Syntax_isOfKind(v_docs_1648_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_docs_1648_);
lean_dec(v_x_1633_);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1756_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1755_, v_a_1634_, v_a_1635_);
return v___x_1756_;
}
else
{
goto v___jp_1746_;
}
}
else
{
goto v___jp_1746_;
}
v___jp_1649_:
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_docs_1648_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1690_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1690_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1690_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v_env_1659_; lean_object* v_messages_1660_; lean_object* v_scopes_1661_; lean_object* v_usedQuotCtxts_1662_; lean_object* v_nextMacroScope_1663_; lean_object* v_maxRecDepth_1664_; lean_object* v_ngen_1665_; lean_object* v_auxDeclNGen_1666_; lean_object* v_infoState_1667_; lean_object* v_traceState_1668_; lean_object* v_snapshotTasks_1669_; lean_object* v_prevLinterStates_1670_; lean_object* v_codeQualityEntryTasks_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1689_; 
v___x_1658_ = lean_st_ref_take(v___y_1652_);
v_env_1659_ = lean_ctor_get(v___x_1658_, 0);
v_messages_1660_ = lean_ctor_get(v___x_1658_, 1);
v_scopes_1661_ = lean_ctor_get(v___x_1658_, 2);
v_usedQuotCtxts_1662_ = lean_ctor_get(v___x_1658_, 3);
v_nextMacroScope_1663_ = lean_ctor_get(v___x_1658_, 4);
v_maxRecDepth_1664_ = lean_ctor_get(v___x_1658_, 5);
v_ngen_1665_ = lean_ctor_get(v___x_1658_, 6);
v_auxDeclNGen_1666_ = lean_ctor_get(v___x_1658_, 7);
v_infoState_1667_ = lean_ctor_get(v___x_1658_, 8);
v_traceState_1668_ = lean_ctor_get(v___x_1658_, 9);
v_snapshotTasks_1669_ = lean_ctor_get(v___x_1658_, 10);
v_prevLinterStates_1670_ = lean_ctor_get(v___x_1658_, 11);
v_codeQualityEntryTasks_1671_ = lean_ctor_get(v___x_1658_, 12);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1673_ = v___x_1658_;
v_isShared_1674_ = v_isSharedCheck_1689_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1671_);
lean_inc(v_prevLinterStates_1670_);
lean_inc(v_snapshotTasks_1669_);
lean_inc(v_traceState_1668_);
lean_inc(v_infoState_1667_);
lean_inc(v_auxDeclNGen_1666_);
lean_inc(v_ngen_1665_);
lean_inc(v_maxRecDepth_1664_);
lean_inc(v_nextMacroScope_1663_);
lean_inc(v_usedQuotCtxts_1662_);
lean_inc(v_scopes_1661_);
lean_inc(v_messages_1660_);
lean_inc(v_env_1659_);
lean_dec(v___x_1658_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1689_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v_toEnvExtension_1676_; lean_object* v_asyncMode_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1675_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_1676_ = lean_ctor_get(v___x_1675_, 0);
v_asyncMode_1677_ = lean_ctor_get(v_toEnvExtension_1676_, 2);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___y_1650_);
lean_ctor_set(v___x_1678_, 1, v_a_1654_);
v___x_1679_ = lean_box(0);
v___x_1680_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1675_, v_env_1659_, v___x_1678_, v_asyncMode_1677_, v___x_1679_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1680_);
v___x_1682_ = v___x_1673_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_messages_1660_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_scopes_1661_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_usedQuotCtxts_1662_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_nextMacroScope_1663_);
lean_ctor_set(v_reuseFailAlloc_1688_, 5, v_maxRecDepth_1664_);
lean_ctor_set(v_reuseFailAlloc_1688_, 6, v_ngen_1665_);
lean_ctor_set(v_reuseFailAlloc_1688_, 7, v_auxDeclNGen_1666_);
lean_ctor_set(v_reuseFailAlloc_1688_, 8, v_infoState_1667_);
lean_ctor_set(v_reuseFailAlloc_1688_, 9, v_traceState_1668_);
lean_ctor_set(v_reuseFailAlloc_1688_, 10, v_snapshotTasks_1669_);
lean_ctor_set(v_reuseFailAlloc_1688_, 11, v_prevLinterStates_1670_);
lean_ctor_set(v_reuseFailAlloc_1688_, 12, v_codeQualityEntryTasks_1671_);
v___x_1682_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = lean_st_ref_put(v___y_1652_, v___x_1682_);
v___x_1684_ = lean_box(0);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1684_);
v___x_1686_ = v___x_1656_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v___y_1650_);
v_a_1691_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1653_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1653_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
v___jp_1699_:
{
if (v___y_1704_ == 0)
{
lean_dec(v___y_1702_);
v___y_1650_ = v___y_1700_;
v___y_1651_ = v___y_1703_;
v___y_1652_ = v___y_1701_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_docs_1648_);
v___x_1705_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1706_ = l_Lean_MessageData_ofConstName(v___y_1700_, v___x_1643_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1702_, v___x_1709_, v___y_1703_, v___y_1701_);
lean_dec(v___y_1702_);
return v___x_1710_;
}
}
v___jp_1711_:
{
lean_object* v___x_1716_; lean_object* v_env_1717_; uint8_t v___x_1718_; 
v___x_1716_ = lean_st_ref_get(v___y_1715_);
v_env_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_ref(v_env_1717_);
lean_dec(v___x_1716_);
v___x_1718_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1717_, v___y_1712_);
if (v___x_1718_ == 0)
{
v___y_1700_ = v___y_1712_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1713_;
v___y_1703_ = v___y_1714_;
v___y_1704_ = v___x_1645_;
goto v___jp_1699_;
}
else
{
v___y_1700_ = v___y_1712_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1713_;
v___y_1703_ = v___y_1714_;
v___y_1704_ = v___x_1643_;
goto v___jp_1699_;
}
}
v___jp_1719_:
{
lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_box(0);
lean_inc(v___y_1720_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1722_, 0, v___y_1720_);
lean_closure_set(v___f_1722_, 1, v___x_1721_);
v___x_1723_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1722_, v_a_1634_, v_a_1635_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v_env_1726_; lean_object* v___x_1727_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_n(v_a_1724_, 2);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_st_ref_get(v_a_1635_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_ref(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1727_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1726_, v_a_1724_);
if (lean_obj_tag(v___x_1727_) == 1)
{
lean_object* v_val_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v_docs_1648_);
v_val_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_val_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1730_ = l_Lean_MessageData_ofConstName(v_a_1724_, v___x_1643_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_MessageData_ofConstName(v_val_1728_, v___x_1643_);
v___x_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v___x_1729_);
v___x_1737_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1720_, v___x_1736_, v_a_1634_, v_a_1635_);
lean_dec(v___y_1720_);
return v___x_1737_;
}
else
{
lean_dec(v___x_1727_);
v___y_1712_ = v_a_1724_;
v___y_1713_ = v___y_1720_;
v___y_1714_ = v_a_1634_;
v___y_1715_ = v_a_1635_;
goto v___jp_1711_;
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v___y_1720_);
lean_dec(v_docs_1648_);
v_a_1738_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1723_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1723_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
v___jp_1746_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_unsigned_to_nat(2u);
v___x_1748_ = l_Lean_Syntax_getArg(v_x_1633_, v___x_1747_);
lean_dec(v_x_1633_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v___x_1748_);
v___x_1750_ = l_Lean_Syntax_isOfKind(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v___x_1748_);
lean_dec(v_docs_1648_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1752_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1751_, v_a_1634_, v_a_1635_);
return v___x_1752_;
}
else
{
v___y_1720_ = v___x_1748_;
goto v___jp_1719_;
}
}
else
{
v___y_1720_ = v___x_1748_;
goto v___jp_1719_;
}
}
}
}
else
{
lean_object* v___x_1757_; lean_object* v_cmd_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v___x_1642_);
v___x_1757_ = lean_unsigned_to_nat(1u);
v_cmd_1758_ = l_Lean_Syntax_getArg(v_x_1633_, v___x_1757_);
lean_dec(v_x_1633_);
v___x_1759_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15);
v___x_1760_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_cmd_1758_, v___x_1759_, v_a_1634_, v_a_1635_);
lean_dec(v_cmd_1758_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_1781_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1777_, v___x_1778_, v___x_1779_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_1812_ = l_Lean_addBuiltinDeclarationRanges(v___x_1810_, v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_1814_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_1817_ = l_Lean_stringToMessageData(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v_a_1835_; lean_object* v_doc_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_1827_);
v___x_1905_ = l_Lean_Syntax_isOfKind(v_x_1827_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v_x_1827_);
v___x_1906_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_1907_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1906_, v_a_1828_, v_a_1829_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1908_);
v___x_1910_ = l_Lean_Syntax_isNone(v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1909_);
v___x_1912_ = l_Lean_Syntax_matchesNull(v___x_1909_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v___x_1909_);
lean_dec(v_x_1827_);
v___x_1913_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_1914_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1913_, v_a_1828_, v_a_1829_);
return v___x_1914_;
}
else
{
lean_object* v_doc_1915_; 
v_doc_1915_ = l_Lean_Syntax_getArg(v___x_1909_, v___x_1908_);
lean_dec(v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_doc_1915_);
v___x_1919_ = l_Lean_Syntax_isOfKind(v_doc_1915_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v_doc_1915_);
lean_dec(v_x_1827_);
v___x_1920_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_1921_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1920_, v_a_1828_, v_a_1829_);
return v___x_1921_;
}
else
{
goto v___jp_1916_;
}
}
else
{
goto v___jp_1916_;
}
v___jp_1916_:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_doc_1915_);
v_doc_1870_ = v___x_1917_;
v___y_1871_ = v_a_1828_;
v___y_1872_ = v_a_1829_;
goto v___jp_1869_;
}
}
}
else
{
lean_object* v___x_1922_; 
lean_dec(v___x_1909_);
v___x_1922_ = lean_box(0);
v_doc_1870_ = v___x_1922_;
v___y_1871_ = v_a_1828_;
v___y_1872_ = v_a_1829_;
goto v___jp_1869_;
}
}
v___jp_1831_:
{
lean_object* v___x_1836_; lean_object* v_env_1837_; lean_object* v_messages_1838_; lean_object* v_scopes_1839_; lean_object* v_usedQuotCtxts_1840_; lean_object* v_nextMacroScope_1841_; lean_object* v_maxRecDepth_1842_; lean_object* v_ngen_1843_; lean_object* v_auxDeclNGen_1844_; lean_object* v_infoState_1845_; lean_object* v_traceState_1846_; lean_object* v_snapshotTasks_1847_; lean_object* v_prevLinterStates_1848_; lean_object* v_codeQualityEntryTasks_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1868_; 
v___x_1836_ = lean_st_ref_take(v___y_1833_);
v_env_1837_ = lean_ctor_get(v___x_1836_, 0);
v_messages_1838_ = lean_ctor_get(v___x_1836_, 1);
v_scopes_1839_ = lean_ctor_get(v___x_1836_, 2);
v_usedQuotCtxts_1840_ = lean_ctor_get(v___x_1836_, 3);
v_nextMacroScope_1841_ = lean_ctor_get(v___x_1836_, 4);
v_maxRecDepth_1842_ = lean_ctor_get(v___x_1836_, 5);
v_ngen_1843_ = lean_ctor_get(v___x_1836_, 6);
v_auxDeclNGen_1844_ = lean_ctor_get(v___x_1836_, 7);
v_infoState_1845_ = lean_ctor_get(v___x_1836_, 8);
v_traceState_1846_ = lean_ctor_get(v___x_1836_, 9);
v_snapshotTasks_1847_ = lean_ctor_get(v___x_1836_, 10);
v_prevLinterStates_1848_ = lean_ctor_get(v___x_1836_, 11);
v_codeQualityEntryTasks_1849_ = lean_ctor_get(v___x_1836_, 12);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1851_ = v___x_1836_;
v_isShared_1852_ = v_isSharedCheck_1868_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1849_);
lean_inc(v_prevLinterStates_1848_);
lean_inc(v_snapshotTasks_1847_);
lean_inc(v_traceState_1846_);
lean_inc(v_infoState_1845_);
lean_inc(v_auxDeclNGen_1844_);
lean_inc(v_ngen_1843_);
lean_inc(v_maxRecDepth_1842_);
lean_inc(v_nextMacroScope_1841_);
lean_inc(v_usedQuotCtxts_1840_);
lean_inc(v_scopes_1839_);
lean_inc(v_messages_1838_);
lean_inc(v_env_1837_);
lean_dec(v___x_1836_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1868_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v_toEnvExtension_1854_; lean_object* v_asyncMode_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1853_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1854_ = lean_ctor_get(v___x_1853_, 0);
v_asyncMode_1855_ = lean_ctor_get(v_toEnvExtension_1854_, 2);
v___x_1856_ = lean_box(0);
v___x_1857_ = l_Lean_TSyntax_getId(v___y_1832_);
lean_dec(v___y_1832_);
v___x_1858_ = l_Lean_TSyntax_getString(v___y_1834_);
lean_dec(v___y_1834_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v_a_1835_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1857_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_box(0);
v___x_1862_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1853_, v_env_1837_, v___x_1860_, v_asyncMode_1855_, v___x_1861_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1862_);
v___x_1864_ = v___x_1851_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_messages_1838_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_scopes_1839_);
lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_usedQuotCtxts_1840_);
lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_nextMacroScope_1841_);
lean_ctor_set(v_reuseFailAlloc_1867_, 5, v_maxRecDepth_1842_);
lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_ngen_1843_);
lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_auxDeclNGen_1844_);
lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_infoState_1845_);
lean_ctor_set(v_reuseFailAlloc_1867_, 9, v_traceState_1846_);
lean_ctor_set(v_reuseFailAlloc_1867_, 10, v_snapshotTasks_1847_);
lean_ctor_set(v_reuseFailAlloc_1867_, 11, v_prevLinterStates_1848_);
lean_ctor_set(v_reuseFailAlloc_1867_, 12, v_codeQualityEntryTasks_1849_);
v___x_1864_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_st_ref_put(v___y_1833_, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1856_);
return v___x_1866_;
}
}
}
v___jp_1869_:
{
lean_object* v___x_1873_; lean_object* v_tag_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1873_ = lean_unsigned_to_nat(2u);
v_tag_1874_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1873_);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v_tag_1874_);
v___x_1876_ = l_Lean_Syntax_isOfKind(v_tag_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_tag_1874_);
lean_dec(v_doc_1870_);
lean_dec(v_x_1827_);
v___x_1877_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_1878_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1877_, v___y_1871_, v___y_1872_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; lean_object* v_user_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1879_ = lean_unsigned_to_nat(3u);
v_user_1880_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1879_);
lean_dec(v_x_1827_);
v___x_1881_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_1880_);
v___x_1882_ = l_Lean_Syntax_isOfKind(v_user_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v_user_1880_);
lean_dec(v_tag_1874_);
lean_dec(v_doc_1870_);
v___x_1883_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_1884_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1883_, v___y_1871_, v___y_1872_);
return v___x_1884_;
}
else
{
if (lean_obj_tag(v_doc_1870_) == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_box(0);
v___y_1832_ = v_tag_1874_;
v___y_1833_ = v___y_1872_;
v___y_1834_ = v_user_1880_;
v_a_1835_ = v___x_1885_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1903_; 
v_val_1886_ = lean_ctor_get(v_doc_1870_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_doc_1870_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1888_ = v_doc_1870_;
v_isShared_1889_ = v_isSharedCheck_1903_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_dec(v_doc_1870_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1903_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; 
v___x_1890_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_val_1886_, v___y_1871_, v___y_1872_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v_a_1891_);
v___x_1893_ = v___x_1888_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
v___y_1832_ = v_tag_1874_;
v___y_1833_ = v___y_1872_;
v___y_1834_ = v_user_1880_;
v_a_1835_ = v___x_1893_;
goto v___jp_1831_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_del_object(v___x_1888_);
lean_dec(v_user_1880_);
lean_dec(v_tag_1874_);
v_a_1895_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1890_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1890_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_1923_, v_a_1924_, v_a_1925_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1936_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1937_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_1938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_1939_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_1940_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1936_, v___x_1937_, v___x_1938_, v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_1970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_1971_ = l_Lean_addBuiltinDeclarationRanges(v___x_1969_, v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_1974_, lean_object* v_x_1975_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
return v___x_1976_;
}
else
{
lean_dec_ref(v___x_1974_);
lean_inc_ref(v_x_1975_);
return v_x_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_1977_, v_x_1978_);
lean_dec(v_x_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_1980_, lean_object* v_k_1981_, lean_object* v_t_1982_){
_start:
{
if (lean_obj_tag(v_t_1982_) == 0)
{
lean_object* v_size_1983_; lean_object* v_k_1984_; lean_object* v_v_1985_; lean_object* v_l_1986_; lean_object* v_r_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2313_; 
v_size_1983_ = lean_ctor_get(v_t_1982_, 0);
v_k_1984_ = lean_ctor_get(v_t_1982_, 1);
v_v_1985_ = lean_ctor_get(v_t_1982_, 2);
v_l_1986_ = lean_ctor_get(v_t_1982_, 3);
v_r_1987_ = lean_ctor_get(v_t_1982_, 4);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_t_1982_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_1989_ = v_t_1982_;
v_isShared_1990_ = v_isSharedCheck_2313_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_r_1987_);
lean_inc(v_l_1986_);
lean_inc(v_v_1985_);
lean_inc(v_k_1984_);
lean_inc(v_size_1983_);
lean_dec(v_t_1982_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2313_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint8_t v___x_1991_; 
v___x_1991_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1981_, v_k_1984_);
switch(v___x_1991_)
{
case 0:
{
lean_object* v_impl_1992_; lean_object* v___x_1993_; 
lean_del_object(v___x_1989_);
lean_dec(v_size_1983_);
v_impl_1992_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1980_, v_k_1981_, v_l_1986_);
v___x_1993_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1984_, v_v_1985_, v_impl_1992_, v_r_1987_);
return v___x_1993_;
}
case 1:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec(v_k_1984_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_v_1985_);
v___x_1995_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_1980_, v___x_1994_);
lean_dec_ref_known(v___x_1994_, 1);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_del_object(v___x_1989_);
lean_dec(v_size_1983_);
lean_dec(v_k_1981_);
if (lean_obj_tag(v_l_1986_) == 0)
{
if (lean_obj_tag(v_r_1987_) == 0)
{
lean_object* v_size_1996_; lean_object* v_k_1997_; lean_object* v_v_1998_; lean_object* v_l_1999_; lean_object* v_r_2000_; lean_object* v_size_2001_; lean_object* v_k_2002_; lean_object* v_v_2003_; lean_object* v_l_2004_; lean_object* v_r_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_size_1996_ = lean_ctor_get(v_l_1986_, 0);
v_k_1997_ = lean_ctor_get(v_l_1986_, 1);
v_v_1998_ = lean_ctor_get(v_l_1986_, 2);
v_l_1999_ = lean_ctor_get(v_l_1986_, 3);
v_r_2000_ = lean_ctor_get(v_l_1986_, 4);
lean_inc(v_r_2000_);
v_size_2001_ = lean_ctor_get(v_r_1987_, 0);
v_k_2002_ = lean_ctor_get(v_r_1987_, 1);
v_v_2003_ = lean_ctor_get(v_r_1987_, 2);
v_l_2004_ = lean_ctor_get(v_r_1987_, 3);
lean_inc(v_l_2004_);
v_r_2005_ = lean_ctor_get(v_r_1987_, 4);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_dec_lt(v_size_1996_, v_size_2001_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2143_; 
lean_inc(v_l_1999_);
lean_inc(v_v_1998_);
lean_inc(v_k_1997_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_l_1986_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; 
v_unused_2144_ = lean_ctor_get(v_l_1986_, 4);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_l_1986_, 3);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_l_1986_, 2);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_1986_, 1);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_1986_, 0);
lean_dec(v_unused_2148_);
v___x_2009_ = v_l_1986_;
v_isShared_2010_ = v_isSharedCheck_2143_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v_l_1986_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2143_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v_tree_2012_; 
v___x_2011_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1997_, v_v_1998_, v_l_1999_, v_r_2000_);
v_tree_2012_ = lean_ctor_get(v___x_2011_, 2);
lean_inc(v_tree_2012_);
if (lean_obj_tag(v_tree_2012_) == 0)
{
lean_object* v_k_2013_; lean_object* v_v_2014_; lean_object* v_size_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_k_2013_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_k_2013_);
v_v_2014_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_v_2014_);
lean_dec_ref(v___x_2011_);
v_size_2015_ = lean_ctor_get(v_tree_2012_, 0);
v___x_2016_ = lean_unsigned_to_nat(3u);
v___x_2017_ = lean_nat_mul(v___x_2016_, v_size_2015_);
v___x_2018_ = lean_nat_dec_lt(v___x_2017_, v_size_2001_);
lean_dec(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_dec(v_l_2004_);
v___x_2019_ = lean_nat_add(v___x_2006_, v_size_2015_);
v___x_2020_ = lean_nat_add(v___x_2019_, v_size_2001_);
lean_dec(v___x_2019_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_r_1987_);
lean_ctor_set(v___x_2009_, 3, v_tree_2012_);
lean_ctor_set(v___x_2009_, 2, v_v_2014_);
lean_ctor_set(v___x_2009_, 1, v_k_2013_);
lean_ctor_set(v___x_2009_, 0, v___x_2020_);
v___x_2022_ = v___x_2009_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_2013_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_tree_2012_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v_r_1987_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
else
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2078_; 
lean_inc(v_r_2005_);
lean_inc(v_v_2003_);
lean_inc(v_k_2002_);
lean_inc(v_size_2001_);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_r_1987_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; lean_object* v_unused_2080_; lean_object* v_unused_2081_; lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2079_ = lean_ctor_get(v_r_1987_, 4);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_r_1987_, 3);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_r_1987_, 2);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_r_1987_, 1);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_r_1987_, 0);
lean_dec(v_unused_2083_);
v___x_2025_ = v_r_1987_;
v_isShared_2026_ = v_isSharedCheck_2078_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v_r_1987_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2078_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v_size_2027_; lean_object* v_k_2028_; lean_object* v_v_2029_; lean_object* v_l_2030_; lean_object* v_r_2031_; lean_object* v_size_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_size_2027_ = lean_ctor_get(v_l_2004_, 0);
v_k_2028_ = lean_ctor_get(v_l_2004_, 1);
v_v_2029_ = lean_ctor_get(v_l_2004_, 2);
v_l_2030_ = lean_ctor_get(v_l_2004_, 3);
v_r_2031_ = lean_ctor_get(v_l_2004_, 4);
v_size_2032_ = lean_ctor_get(v_r_2005_, 0);
v___x_2033_ = lean_unsigned_to_nat(2u);
v___x_2034_ = lean_nat_mul(v___x_2033_, v_size_2032_);
v___x_2035_ = lean_nat_dec_lt(v_size_2027_, v___x_2034_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2063_; 
lean_inc(v_r_2031_);
lean_inc(v_l_2030_);
lean_inc(v_v_2029_);
lean_inc(v_k_2028_);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_l_2004_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; lean_object* v_unused_2065_; lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; 
v_unused_2064_ = lean_ctor_get(v_l_2004_, 4);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_l_2004_, 3);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_l_2004_, 2);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_l_2004_, 1);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_l_2004_, 0);
lean_dec(v_unused_2068_);
v___x_2037_ = v_l_2004_;
v_isShared_2038_ = v_isSharedCheck_2063_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v_l_2004_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2063_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2053_; 
v___x_2039_ = lean_nat_add(v___x_2006_, v_size_2015_);
v___x_2040_ = lean_nat_add(v___x_2039_, v_size_2001_);
lean_dec(v_size_2001_);
if (lean_obj_tag(v_l_2030_) == 0)
{
lean_object* v_size_2061_; 
v_size_2061_ = lean_ctor_get(v_l_2030_, 0);
lean_inc(v_size_2061_);
v___y_2053_ = v_size_2061_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_unsigned_to_nat(0u);
v___y_2053_ = v___x_2062_;
goto v___jp_2052_;
}
v___jp_2041_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_nat_add(v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec(v___y_2043_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 4, v_r_2005_);
lean_ctor_set(v___x_2037_, 3, v_r_2031_);
lean_ctor_set(v___x_2037_, 2, v_v_2003_);
lean_ctor_set(v___x_2037_, 1, v_k_2002_);
lean_ctor_set(v___x_2037_, 0, v___x_2045_);
v___x_2047_ = v___x_2037_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_2002_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_2003_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_r_2031_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_r_2005_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 4, v___x_2047_);
lean_ctor_set(v___x_2025_, 3, v___y_2042_);
lean_ctor_set(v___x_2025_, 2, v_v_2029_);
lean_ctor_set(v___x_2025_, 1, v_k_2028_);
lean_ctor_set(v___x_2025_, 0, v___x_2040_);
v___x_2049_ = v___x_2025_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_k_2028_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_v_2029_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v___y_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
v___jp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_nat_add(v___x_2039_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec(v___x_2039_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_l_2030_);
lean_ctor_set(v___x_2009_, 3, v_tree_2012_);
lean_ctor_set(v___x_2009_, 2, v_v_2014_);
lean_ctor_set(v___x_2009_, 1, v_k_2013_);
lean_ctor_set(v___x_2009_, 0, v___x_2054_);
v___x_2056_ = v___x_2009_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_k_2013_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_v_2014_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_tree_2012_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_l_2030_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_nat_add(v___x_2006_, v_size_2032_);
if (lean_obj_tag(v_r_2031_) == 0)
{
lean_object* v_size_2058_; 
v_size_2058_ = lean_ctor_get(v_r_2031_, 0);
lean_inc(v_size_2058_);
v___y_2042_ = v___x_2056_;
v___y_2043_ = v___x_2057_;
v___y_2044_ = v_size_2058_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___y_2042_ = v___x_2056_;
v___y_2043_ = v___x_2057_;
v___y_2044_ = v___x_2059_;
goto v___jp_2041_;
}
}
}
}
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2069_ = lean_nat_add(v___x_2006_, v_size_2015_);
v___x_2070_ = lean_nat_add(v___x_2069_, v_size_2001_);
lean_dec(v_size_2001_);
v___x_2071_ = lean_nat_add(v___x_2069_, v_size_2027_);
lean_dec(v___x_2069_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 4, v_l_2004_);
lean_ctor_set(v___x_2025_, 3, v_tree_2012_);
lean_ctor_set(v___x_2025_, 2, v_v_2014_);
lean_ctor_set(v___x_2025_, 1, v_k_2013_);
lean_ctor_set(v___x_2025_, 0, v___x_2071_);
v___x_2073_ = v___x_2025_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_k_2013_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_v_2014_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_tree_2012_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_l_2004_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_r_2005_);
lean_ctor_set(v___x_2009_, 3, v___x_2073_);
lean_ctor_set(v___x_2009_, 2, v_v_2003_);
lean_ctor_set(v___x_2009_, 1, v_k_2002_);
lean_ctor_set(v___x_2009_, 0, v___x_2070_);
v___x_2075_ = v___x_2009_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2002_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2003_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_r_2005_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
else
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2137_; 
lean_inc(v_r_2005_);
lean_inc(v_v_2003_);
lean_inc(v_k_2002_);
lean_inc(v_size_2001_);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_r_1987_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; lean_object* v_unused_2139_; lean_object* v_unused_2140_; lean_object* v_unused_2141_; lean_object* v_unused_2142_; 
v_unused_2138_ = lean_ctor_get(v_r_1987_, 4);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v_r_1987_, 3);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_r_1987_, 2);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_r_1987_, 1);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_r_1987_, 0);
lean_dec(v_unused_2142_);
v___x_2085_ = v_r_1987_;
v_isShared_2086_ = v_isSharedCheck_2137_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v_r_1987_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2137_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
if (lean_obj_tag(v_l_2004_) == 0)
{
if (lean_obj_tag(v_r_2005_) == 0)
{
lean_object* v_k_2087_; lean_object* v_v_2088_; lean_object* v_size_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v_k_2087_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_k_2087_);
v_v_2088_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_v_2088_);
lean_dec_ref(v___x_2011_);
v_size_2089_ = lean_ctor_get(v_l_2004_, 0);
v___x_2090_ = lean_nat_add(v___x_2006_, v_size_2001_);
lean_dec(v_size_2001_);
v___x_2091_ = lean_nat_add(v___x_2006_, v_size_2089_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 4, v_l_2004_);
lean_ctor_set(v___x_2085_, 3, v_tree_2012_);
lean_ctor_set(v___x_2085_, 2, v_v_2088_);
lean_ctor_set(v___x_2085_, 1, v_k_2087_);
lean_ctor_set(v___x_2085_, 0, v___x_2091_);
v___x_2093_ = v___x_2085_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_2087_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_2088_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_tree_2012_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_l_2004_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_r_2005_);
lean_ctor_set(v___x_2009_, 3, v___x_2093_);
lean_ctor_set(v___x_2009_, 2, v_v_2003_);
lean_ctor_set(v___x_2009_, 1, v_k_2002_);
lean_ctor_set(v___x_2009_, 0, v___x_2090_);
v___x_2095_ = v___x_2009_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2002_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2003_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_r_2005_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_k_2098_; lean_object* v_v_2099_; lean_object* v_k_2100_; lean_object* v_v_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_size_2001_);
v_k_2098_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_k_2098_);
v_v_2099_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_v_2099_);
lean_dec_ref(v___x_2011_);
v_k_2100_ = lean_ctor_get(v_l_2004_, 1);
v_v_2101_ = lean_ctor_get(v_l_2004_, 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_l_2004_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; 
v_unused_2116_ = lean_ctor_get(v_l_2004_, 4);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_l_2004_, 3);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_l_2004_, 0);
lean_dec(v_unused_2118_);
v___x_2103_ = v_l_2004_;
v_isShared_2104_ = v_isSharedCheck_2115_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_v_2101_);
lean_inc(v_k_2100_);
lean_dec(v_l_2004_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2115_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_unsigned_to_nat(3u);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v_r_2005_);
lean_ctor_set(v___x_2103_, 3, v_r_2005_);
lean_ctor_set(v___x_2103_, 2, v_v_2099_);
lean_ctor_set(v___x_2103_, 1, v_k_2098_);
lean_ctor_set(v___x_2103_, 0, v___x_2006_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_2098_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_2099_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_r_2005_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_r_2005_);
v___x_2107_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 3, v_r_2005_);
lean_ctor_set(v___x_2085_, 0, v___x_2006_);
v___x_2109_ = v___x_2085_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_2002_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_2003_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_r_2005_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_r_2005_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___x_2109_);
lean_ctor_set(v___x_2009_, 3, v___x_2107_);
lean_ctor_set(v___x_2009_, 2, v_v_2101_);
lean_ctor_set(v___x_2009_, 1, v_k_2100_);
lean_ctor_set(v___x_2009_, 0, v___x_2105_);
v___x_2111_ = v___x_2009_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2100_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2005_) == 0)
{
lean_object* v_k_2119_; lean_object* v_v_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_size_2001_);
v_k_2119_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_k_2119_);
v_v_2120_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_v_2120_);
lean_dec_ref(v___x_2011_);
v___x_2121_ = lean_unsigned_to_nat(3u);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 4, v_l_2004_);
lean_ctor_set(v___x_2085_, 2, v_v_2120_);
lean_ctor_set(v___x_2085_, 1, v_k_2119_);
lean_ctor_set(v___x_2085_, 0, v___x_2006_);
v___x_2123_ = v___x_2085_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_k_2119_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_v_2120_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_l_2004_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v_l_2004_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_r_2005_);
lean_ctor_set(v___x_2009_, 3, v___x_2123_);
lean_ctor_set(v___x_2009_, 2, v_v_2003_);
lean_ctor_set(v___x_2009_, 1, v_k_2002_);
lean_ctor_set(v___x_2009_, 0, v___x_2121_);
v___x_2125_ = v___x_2009_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_2002_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_2003_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_r_2005_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_k_2128_; lean_object* v_v_2129_; lean_object* v___x_2131_; 
v_k_2128_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_k_2128_);
v_v_2129_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_v_2129_);
lean_dec_ref(v___x_2011_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 3, v_r_2005_);
v___x_2131_ = v___x_2085_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_size_2001_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_k_2002_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_v_2003_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_r_2005_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_r_2005_);
v___x_2131_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = lean_unsigned_to_nat(2u);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___x_2131_);
lean_ctor_set(v___x_2009_, 3, v_r_2005_);
lean_ctor_set(v___x_2009_, 2, v_v_2129_);
lean_ctor_set(v___x_2009_, 1, v_k_2128_);
lean_ctor_set(v___x_2009_, 0, v___x_2132_);
v___x_2134_ = v___x_2009_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_k_2128_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_v_2129_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_r_2005_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v___x_2131_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
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
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2301_; 
lean_inc(v_r_2005_);
lean_inc(v_v_2003_);
lean_inc(v_k_2002_);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_r_1987_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; lean_object* v_unused_2303_; lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; 
v_unused_2302_ = lean_ctor_get(v_r_1987_, 4);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_r_1987_, 3);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_r_1987_, 2);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_r_1987_, 1);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_r_1987_, 0);
lean_dec(v_unused_2306_);
v___x_2150_ = v_r_1987_;
v_isShared_2151_ = v_isSharedCheck_2301_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v_r_1987_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2301_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v_tree_2153_; 
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2002_, v_v_2003_, v_l_2004_, v_r_2005_);
v_tree_2153_ = lean_ctor_get(v___x_2152_, 2);
lean_inc(v_tree_2153_);
if (lean_obj_tag(v_tree_2153_) == 0)
{
lean_object* v_k_2154_; lean_object* v_v_2155_; lean_object* v_size_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_k_2154_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_k_2154_);
v_v_2155_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_v_2155_);
lean_dec_ref(v___x_2152_);
v_size_2156_ = lean_ctor_get(v_tree_2153_, 0);
v___x_2157_ = lean_unsigned_to_nat(3u);
v___x_2158_ = lean_nat_mul(v___x_2157_, v_size_2156_);
v___x_2159_ = lean_nat_dec_lt(v___x_2158_, v_size_1996_);
lean_dec(v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec(v_r_2000_);
v___x_2160_ = lean_nat_add(v___x_2006_, v_size_1996_);
v___x_2161_ = lean_nat_add(v___x_2160_, v_size_2156_);
lean_dec(v___x_2160_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_tree_2153_);
lean_ctor_set(v___x_2150_, 3, v_l_1986_);
lean_ctor_set(v___x_2150_, 2, v_v_2155_);
lean_ctor_set(v___x_2150_, 1, v_k_2154_);
lean_ctor_set(v___x_2150_, 0, v___x_2161_);
v___x_2163_ = v___x_2150_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2154_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2155_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_l_1986_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_tree_2153_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
else
{
lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2230_; 
lean_inc(v_l_1999_);
lean_inc(v_v_1998_);
lean_inc(v_k_1997_);
lean_inc(v_size_1996_);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_l_1986_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; 
v_unused_2231_ = lean_ctor_get(v_l_1986_, 4);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_l_1986_, 3);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_l_1986_, 2);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_l_1986_, 1);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_l_1986_, 0);
lean_dec(v_unused_2235_);
v___x_2166_ = v_l_1986_;
v_isShared_2167_ = v_isSharedCheck_2230_;
goto v_resetjp_2165_;
}
else
{
lean_dec(v_l_1986_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2230_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_size_2168_; lean_object* v_size_2169_; lean_object* v_k_2170_; lean_object* v_v_2171_; lean_object* v_l_2172_; lean_object* v_r_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_size_2168_ = lean_ctor_get(v_l_1999_, 0);
v_size_2169_ = lean_ctor_get(v_r_2000_, 0);
v_k_2170_ = lean_ctor_get(v_r_2000_, 1);
v_v_2171_ = lean_ctor_get(v_r_2000_, 2);
v_l_2172_ = lean_ctor_get(v_r_2000_, 3);
v_r_2173_ = lean_ctor_get(v_r_2000_, 4);
v___x_2174_ = lean_unsigned_to_nat(2u);
v___x_2175_ = lean_nat_mul(v___x_2174_, v_size_2168_);
v___x_2176_ = lean_nat_dec_lt(v_size_2169_, v___x_2175_);
lean_dec(v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2214_; 
lean_inc(v_r_2173_);
lean_inc(v_l_2172_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
lean_del_object(v___x_2166_);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_r_2000_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; lean_object* v_unused_2216_; lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; 
v_unused_2215_ = lean_ctor_get(v_r_2000_, 4);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_r_2000_, 3);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_r_2000_, 2);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_r_2000_, 1);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_r_2000_, 0);
lean_dec(v_unused_2219_);
v___x_2178_ = v_r_2000_;
v_isShared_2179_ = v_isSharedCheck_2214_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v_r_2000_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2214_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___x_2202_; lean_object* v___y_2204_; 
v___x_2180_ = lean_nat_add(v___x_2006_, v_size_1996_);
lean_dec(v_size_1996_);
v___x_2181_ = lean_nat_add(v___x_2180_, v_size_2156_);
lean_dec(v___x_2180_);
v___x_2202_ = lean_nat_add(v___x_2006_, v_size_2168_);
if (lean_obj_tag(v_l_2172_) == 0)
{
lean_object* v_size_2212_; 
v_size_2212_ = lean_ctor_get(v_l_2172_, 0);
lean_inc(v_size_2212_);
v___y_2204_ = v_size_2212_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_unsigned_to_nat(0u);
v___y_2204_ = v___x_2213_;
goto v___jp_2203_;
}
v___jp_2182_:
{
lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2186_ = lean_nat_add(v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec(v___y_2184_);
lean_inc_ref(v_tree_2153_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_tree_2153_);
lean_ctor_set(v___x_2178_, 3, v_r_2173_);
lean_ctor_set(v___x_2178_, 2, v_v_2155_);
lean_ctor_set(v___x_2178_, 1, v_k_2154_);
lean_ctor_set(v___x_2178_, 0, v___x_2186_);
v___x_2188_ = v___x_2178_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2154_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2155_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_2173_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_tree_2153_);
v___x_2188_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_isSharedCheck_2195_ = !lean_is_exclusive(v_tree_2153_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; lean_object* v_unused_2197_; lean_object* v_unused_2198_; lean_object* v_unused_2199_; lean_object* v_unused_2200_; 
v_unused_2196_ = lean_ctor_get(v_tree_2153_, 4);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_tree_2153_, 3);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_tree_2153_, 2);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_tree_2153_, 1);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_tree_2153_, 0);
lean_dec(v_unused_2200_);
v___x_2190_ = v_tree_2153_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_dec(v_tree_2153_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 4, v___x_2188_);
lean_ctor_set(v___x_2190_, 3, v___y_2183_);
lean_ctor_set(v___x_2190_, 2, v_v_2171_);
lean_ctor_set(v___x_2190_, 1, v_k_2170_);
lean_ctor_set(v___x_2190_, 0, v___x_2181_);
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v___y_2183_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v___x_2188_);
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
v___jp_2203_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_nat_add(v___x_2202_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec(v___x_2202_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_l_2172_);
lean_ctor_set(v___x_2150_, 3, v_l_1999_);
lean_ctor_set(v___x_2150_, 2, v_v_1998_);
lean_ctor_set(v___x_2150_, 1, v_k_1997_);
lean_ctor_set(v___x_2150_, 0, v___x_2205_);
v___x_2207_ = v___x_2150_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_l_2172_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_nat_add(v___x_2006_, v_size_2156_);
if (lean_obj_tag(v_r_2173_) == 0)
{
lean_object* v_size_2209_; 
v_size_2209_ = lean_ctor_get(v_r_2173_, 0);
lean_inc(v_size_2209_);
v___y_2183_ = v___x_2207_;
v___y_2184_ = v___x_2208_;
v___y_2185_ = v_size_2209_;
goto v___jp_2182_;
}
else
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_unsigned_to_nat(0u);
v___y_2183_ = v___x_2207_;
v___y_2184_ = v___x_2208_;
v___y_2185_ = v___x_2210_;
goto v___jp_2182_;
}
}
}
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2220_ = lean_nat_add(v___x_2006_, v_size_1996_);
lean_dec(v_size_1996_);
v___x_2221_ = lean_nat_add(v___x_2220_, v_size_2156_);
lean_dec(v___x_2220_);
v___x_2222_ = lean_nat_add(v___x_2006_, v_size_2156_);
v___x_2223_ = lean_nat_add(v___x_2222_, v_size_2169_);
lean_dec(v___x_2222_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_tree_2153_);
lean_ctor_set(v___x_2150_, 3, v_r_2000_);
lean_ctor_set(v___x_2150_, 2, v_v_2155_);
lean_ctor_set(v___x_2150_, 1, v_k_2154_);
lean_ctor_set(v___x_2150_, 0, v___x_2223_);
v___x_2225_ = v___x_2150_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2154_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2155_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_r_2000_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_tree_2153_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 4, v___x_2225_);
lean_ctor_set(v___x_2166_, 0, v___x_2221_);
v___x_2227_ = v___x_2166_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1999_) == 0)
{
lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2259_; 
lean_inc_ref(v_l_1999_);
lean_inc(v_v_1998_);
lean_inc(v_k_1997_);
lean_inc(v_size_1996_);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_l_1986_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; lean_object* v_unused_2264_; 
v_unused_2260_ = lean_ctor_get(v_l_1986_, 4);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_l_1986_, 3);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_l_1986_, 2);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_l_1986_, 1);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_l_1986_, 0);
lean_dec(v_unused_2264_);
v___x_2237_ = v_l_1986_;
v_isShared_2238_ = v_isSharedCheck_2259_;
goto v_resetjp_2236_;
}
else
{
lean_dec(v_l_1986_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2259_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
if (lean_obj_tag(v_r_2000_) == 0)
{
lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v_size_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v_k_2239_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_k_2239_);
v_v_2240_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_v_2240_);
lean_dec_ref(v___x_2152_);
v_size_2241_ = lean_ctor_get(v_r_2000_, 0);
v___x_2242_ = lean_nat_add(v___x_2006_, v_size_1996_);
lean_dec(v_size_1996_);
v___x_2243_ = lean_nat_add(v___x_2006_, v_size_2241_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_tree_2153_);
lean_ctor_set(v___x_2150_, 3, v_r_2000_);
lean_ctor_set(v___x_2150_, 2, v_v_2240_);
lean_ctor_set(v___x_2150_, 1, v_k_2239_);
lean_ctor_set(v___x_2150_, 0, v___x_2243_);
v___x_2245_ = v___x_2150_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_r_2000_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_tree_2153_);
v___x_2245_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2247_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v___x_2245_);
lean_ctor_set(v___x_2237_, 0, v___x_2242_);
v___x_2247_ = v___x_2237_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_k_2250_; lean_object* v_v_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
lean_dec(v_size_1996_);
v_k_2250_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_k_2250_);
v_v_2251_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_v_2251_);
lean_dec_ref(v___x_2152_);
v___x_2252_ = lean_unsigned_to_nat(3u);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_r_2000_);
lean_ctor_set(v___x_2150_, 3, v_r_2000_);
lean_ctor_set(v___x_2150_, 2, v_v_2251_);
lean_ctor_set(v___x_2150_, 1, v_k_2250_);
lean_ctor_set(v___x_2150_, 0, v___x_2006_);
v___x_2254_ = v___x_2150_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_k_2250_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_v_2251_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_r_2000_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_r_2000_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v___x_2254_);
lean_ctor_set(v___x_2237_, 0, v___x_2252_);
v___x_2256_ = v___x_2237_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2000_) == 0)
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2289_; 
lean_inc(v_l_1999_);
lean_inc(v_v_1998_);
lean_inc(v_k_1997_);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_l_1986_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; lean_object* v_unused_2291_; lean_object* v_unused_2292_; lean_object* v_unused_2293_; lean_object* v_unused_2294_; 
v_unused_2290_ = lean_ctor_get(v_l_1986_, 4);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_l_1986_, 3);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_l_1986_, 2);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_l_1986_, 1);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_l_1986_, 0);
lean_dec(v_unused_2294_);
v___x_2266_ = v_l_1986_;
v_isShared_2267_ = v_isSharedCheck_2289_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v_l_1986_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2289_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_k_2268_; lean_object* v_v_2269_; lean_object* v_k_2270_; lean_object* v_v_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2285_; 
v_k_2268_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_k_2268_);
v_v_2269_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_v_2269_);
lean_dec_ref(v___x_2152_);
v_k_2270_ = lean_ctor_get(v_r_2000_, 1);
v_v_2271_ = lean_ctor_get(v_r_2000_, 2);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_r_2000_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; lean_object* v_unused_2287_; lean_object* v_unused_2288_; 
v_unused_2286_ = lean_ctor_get(v_r_2000_, 4);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_r_2000_, 3);
lean_dec(v_unused_2287_);
v_unused_2288_ = lean_ctor_get(v_r_2000_, 0);
lean_dec(v_unused_2288_);
v___x_2273_ = v_r_2000_;
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_v_2271_);
lean_inc(v_k_2270_);
lean_dec(v_r_2000_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_unsigned_to_nat(3u);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 4, v_l_1999_);
lean_ctor_set(v___x_2273_, 3, v_l_1999_);
lean_ctor_set(v___x_2273_, 2, v_v_1998_);
lean_ctor_set(v___x_2273_, 1, v_k_1997_);
lean_ctor_set(v___x_2273_, 0, v___x_2006_);
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_l_1999_);
v___x_2277_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_l_1999_);
lean_ctor_set(v___x_2150_, 3, v_l_1999_);
lean_ctor_set(v___x_2150_, 2, v_v_2269_);
lean_ctor_set(v___x_2150_, 1, v_k_2268_);
lean_ctor_set(v___x_2150_, 0, v___x_2006_);
v___x_2279_ = v___x_2150_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_k_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_v_2269_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_l_1999_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v___x_2279_);
lean_ctor_set(v___x_2266_, 3, v___x_2277_);
lean_ctor_set(v___x_2266_, 2, v_v_2271_);
lean_ctor_set(v___x_2266_, 1, v_k_2270_);
lean_ctor_set(v___x_2266_, 0, v___x_2275_);
v___x_2281_ = v___x_2266_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2270_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2271_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
lean_object* v_k_2295_; lean_object* v_v_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v_k_2295_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_k_2295_);
v_v_2296_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_v_2296_);
lean_dec_ref(v___x_2152_);
v___x_2297_ = lean_unsigned_to_nat(2u);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 4, v_r_2000_);
lean_ctor_set(v___x_2150_, 3, v_l_1986_);
lean_ctor_set(v___x_2150_, 2, v_v_2296_);
lean_ctor_set(v___x_2150_, 1, v_k_2295_);
lean_ctor_set(v___x_2150_, 0, v___x_2297_);
v___x_2299_ = v___x_2150_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2295_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2296_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_l_1986_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_r_2000_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
}
else
{
return v_l_1986_;
}
}
else
{
return v_r_1987_;
}
}
else
{
lean_object* v_val_2307_; lean_object* v___x_2309_; 
v_val_2307_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v___x_1995_, 1);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 2, v_val_2307_);
lean_ctor_set(v___x_1989_, 1, v_k_1981_);
v___x_2309_ = v___x_1989_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_size_1983_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_k_1981_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_val_2307_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_l_1986_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v_r_1987_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
default: 
{
lean_object* v_impl_2311_; lean_object* v___x_2312_; 
lean_del_object(v___x_1989_);
lean_dec(v_size_1983_);
v_impl_2311_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1980_, v_k_1981_, v_r_1987_);
v___x_2312_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1984_, v_v_1985_, v_l_1986_, v_impl_2311_);
return v___x_2312_;
}
}
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_1980_, v___x_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_dec(v_k_1981_);
return v_t_1982_;
}
else
{
lean_object* v_val_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_val_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_val_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v_k_1981_);
lean_ctor_set(v___x_2318_, 2, v_val_2316_);
lean_ctor_set(v___x_2318_, 3, v_t_1982_);
lean_ctor_set(v___x_2318_, 4, v_t_1982_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2319_, lean_object* v_i_2320_, lean_object* v_k_2321_){
_start:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_array_get_size(v_keys_2319_);
v___x_2323_ = lean_nat_dec_lt(v_i_2320_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_dec(v_i_2320_);
return v___x_2323_;
}
else
{
lean_object* v_k_x27_2324_; uint8_t v___x_2325_; 
v_k_x27_2324_ = lean_array_fget_borrowed(v_keys_2319_, v_i_2320_);
v___x_2325_ = lean_name_eq(v_k_2321_, v_k_x27_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_add(v_i_2320_, v___x_2326_);
lean_dec(v_i_2320_);
v_i_2320_ = v___x_2327_;
goto _start;
}
else
{
lean_dec(v_i_2320_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2329_, lean_object* v_i_2330_, lean_object* v_k_2331_){
_start:
{
uint8_t v_res_2332_; lean_object* v_r_2333_; 
v_res_2332_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2329_, v_i_2330_, v_k_2331_);
lean_dec(v_k_2331_);
lean_dec_ref(v_keys_2329_);
v_r_2333_ = lean_box(v_res_2332_);
return v_r_2333_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_2334_, size_t v_x_2335_, lean_object* v_x_2336_){
_start:
{
if (lean_obj_tag(v_x_2334_) == 0)
{
lean_object* v_es_2337_; lean_object* v___x_2338_; size_t v___x_2339_; size_t v___x_2340_; lean_object* v_j_2341_; lean_object* v___x_2342_; 
v_es_2337_ = lean_ctor_get(v_x_2334_, 0);
v___x_2338_ = lean_box(2);
v___x_2339_ = ((size_t)31ULL);
v___x_2340_ = lean_usize_land(v_x_2335_, v___x_2339_);
v_j_2341_ = lean_usize_to_nat(v___x_2340_);
v___x_2342_ = lean_array_get_borrowed(v___x_2338_, v_es_2337_, v_j_2341_);
lean_dec(v_j_2341_);
switch(lean_obj_tag(v___x_2342_))
{
case 0:
{
lean_object* v_key_2343_; uint8_t v___x_2344_; 
v_key_2343_ = lean_ctor_get(v___x_2342_, 0);
v___x_2344_ = lean_name_eq(v_x_2336_, v_key_2343_);
return v___x_2344_;
}
case 1:
{
lean_object* v_node_2345_; size_t v___x_2346_; size_t v___x_2347_; 
v_node_2345_ = lean_ctor_get(v___x_2342_, 0);
v___x_2346_ = ((size_t)5ULL);
v___x_2347_ = lean_usize_shift_right(v_x_2335_, v___x_2346_);
v_x_2334_ = v_node_2345_;
v_x_2335_ = v___x_2347_;
goto _start;
}
default: 
{
uint8_t v___x_2349_; 
v___x_2349_ = 0;
return v___x_2349_;
}
}
}
else
{
lean_object* v_ks_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_ks_2350_ = lean_ctor_get(v_x_2334_, 0);
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_2350_, v___x_2351_, v_x_2336_);
return v___x_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
size_t v_x_3827__boxed_2356_; uint8_t v_res_2357_; lean_object* v_r_2358_; 
v_x_3827__boxed_2356_ = lean_unbox_usize(v_x_2354_);
lean_dec(v_x_2354_);
v_res_2357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2353_, v_x_3827__boxed_2356_, v_x_2355_);
lean_dec(v_x_2355_);
lean_dec_ref(v_x_2353_);
v_r_2358_ = lean_box(v_res_2357_);
return v_r_2358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_2359_, lean_object* v_x_2360_){
_start:
{
uint64_t v___y_2362_; 
if (lean_obj_tag(v_x_2360_) == 0)
{
uint64_t v___x_2365_; 
v___x_2365_ = 1723ULL;
v___y_2362_ = v___x_2365_;
goto v___jp_2361_;
}
else
{
uint64_t v_hash_2366_; 
v_hash_2366_ = lean_ctor_get_uint64(v_x_2360_, sizeof(void*)*2);
v___y_2362_ = v_hash_2366_;
goto v___jp_2361_;
}
v___jp_2361_:
{
size_t v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_uint64_to_usize(v___y_2362_);
v___x_2364_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2359_, v___x_2363_, v_x_2360_);
return v___x_2364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2367_, v_x_2368_);
lean_dec(v_x_2368_);
lean_dec_ref(v_x_2367_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_2371_, lean_object* v_a_2372_, uint8_t v___x_2373_, lean_object* v_x_2374_, lean_object* v_____s_2375_){
_start:
{
lean_object* v_fst_2376_; lean_object* v_kinds_2377_; uint8_t v___x_2378_; 
v_fst_2376_ = lean_ctor_get(v_x_2374_, 0);
lean_inc(v_fst_2376_);
lean_dec_ref(v_x_2374_);
v_kinds_2377_ = lean_ctor_get(v_tactics_2371_, 1);
v___x_2378_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_2377_, v_fst_2376_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_dec(v_fst_2376_);
lean_dec(v_a_2372_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_____s_2375_);
return v___x_2379_;
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = l_Lean_Name_toString(v_a_2372_, v___x_2373_);
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2380_, v_fst_2376_, v_____s_2375_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_2383_, lean_object* v_a_2384_, lean_object* v___x_2385_, lean_object* v_x_2386_, lean_object* v_____s_2387_){
_start:
{
uint8_t v___x_3883__boxed_2388_; lean_object* v_res_2389_; 
v___x_3883__boxed_2388_ = lean_unbox(v___x_2385_);
v_res_2389_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2383_, v_a_2384_, v___x_3883__boxed_2388_, v_x_2386_, v_____s_2387_);
lean_dec_ref(v_tactics_2383_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_2390_, lean_object* v_keys_2391_, lean_object* v_vals_2392_, lean_object* v_i_2393_, lean_object* v_acc_2394_){
_start:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = lean_array_get_size(v_keys_2391_);
v___x_2396_ = lean_nat_dec_lt(v_i_2393_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; 
lean_dec(v_i_2393_);
lean_dec_ref(v_f_2390_);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_acc_2394_);
return v___x_2397_;
}
else
{
lean_object* v_k_2398_; lean_object* v_v_2399_; lean_object* v___x_2400_; 
v_k_2398_ = lean_array_fget_borrowed(v_keys_2391_, v_i_2393_);
v_v_2399_ = lean_array_fget_borrowed(v_vals_2392_, v_i_2393_);
lean_inc_ref(v_f_2390_);
lean_inc(v_v_2399_);
lean_inc(v_k_2398_);
v___x_2400_ = lean_apply_3(v_f_2390_, v_acc_2394_, v_k_2398_, v_v_2399_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_dec(v_i_2393_);
lean_dec_ref(v_f_2390_);
return v___x_2400_;
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_add(v_i_2393_, v___x_2402_);
lean_dec(v_i_2393_);
v_i_2393_ = v___x_2403_;
v_acc_2394_ = v_a_2401_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_2405_, lean_object* v_keys_2406_, lean_object* v_vals_2407_, lean_object* v_i_2408_, lean_object* v_acc_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2405_, v_keys_2406_, v_vals_2407_, v_i_2408_, v_acc_2409_);
lean_dec_ref(v_vals_2407_);
lean_dec_ref(v_keys_2406_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_2411_, lean_object* v_as_2412_, size_t v_i_2413_, size_t v_stop_2414_, lean_object* v_b_2415_){
_start:
{
lean_object* v_a_2417_; lean_object* v___y_2422_; uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_eq(v_i_2413_, v_stop_2414_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_array_uget_borrowed(v_as_2412_, v_i_2413_);
switch(lean_obj_tag(v___x_2425_))
{
case 0:
{
lean_object* v_key_2426_; lean_object* v_val_2427_; lean_object* v___x_2428_; 
v_key_2426_ = lean_ctor_get(v___x_2425_, 0);
v_val_2427_ = lean_ctor_get(v___x_2425_, 1);
lean_inc_ref(v_f_2411_);
lean_inc(v_val_2427_);
lean_inc(v_key_2426_);
v___x_2428_ = lean_apply_3(v_f_2411_, v_b_2415_, v_key_2426_, v_val_2427_);
v___y_2422_ = v___x_2428_;
goto v___jp_2421_;
}
case 1:
{
lean_object* v_node_2429_; lean_object* v___x_2430_; 
v_node_2429_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_node_2429_);
lean_inc_ref(v_f_2411_);
v___x_2430_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2411_, v_node_2429_, v_b_2415_);
v___y_2422_ = v___x_2430_;
goto v___jp_2421_;
}
default: 
{
v_a_2417_ = v_b_2415_;
goto v___jp_2416_;
}
}
}
else
{
lean_object* v___x_2431_; 
lean_dec_ref(v_f_2411_);
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_b_2415_);
return v___x_2431_;
}
v___jp_2416_:
{
size_t v___x_2418_; size_t v___x_2419_; 
v___x_2418_ = ((size_t)1ULL);
v___x_2419_ = lean_usize_add(v_i_2413_, v___x_2418_);
v_i_2413_ = v___x_2419_;
v_b_2415_ = v_a_2417_;
goto _start;
}
v___jp_2421_:
{
if (lean_obj_tag(v___y_2422_) == 0)
{
lean_dec_ref(v_f_2411_);
return v___y_2422_;
}
else
{
lean_object* v_a_2423_; 
v_a_2423_ = lean_ctor_get(v___y_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___y_2422_, 1);
v_a_2417_ = v_a_2423_;
goto v___jp_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
if (lean_obj_tag(v_x_2433_) == 0)
{
lean_object* v_es_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2448_; 
v_es_2435_ = lean_ctor_get(v_x_2433_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2437_ = v_x_2433_;
v_isShared_2438_ = v_isSharedCheck_2448_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_es_2435_);
lean_dec(v_x_2433_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2448_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_array_get_size(v_es_2435_);
v___x_2441_ = lean_nat_dec_lt(v___x_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref(v_es_2435_);
lean_dec_ref(v_f_2432_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 1);
lean_ctor_set(v___x_2437_, 0, v_x_2434_);
v___x_2443_ = v___x_2437_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_x_2434_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
else
{
size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
lean_del_object(v___x_2437_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = lean_usize_of_nat(v___x_2440_);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2432_, v_es_2435_, v___x_2445_, v___x_2446_, v_x_2434_);
lean_dec_ref(v_es_2435_);
return v___x_2447_;
}
}
}
else
{
lean_object* v_ks_2449_; lean_object* v_vs_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_ks_2449_ = lean_ctor_get(v_x_2433_, 0);
lean_inc_ref(v_ks_2449_);
v_vs_2450_ = lean_ctor_get(v_x_2433_, 1);
lean_inc_ref(v_vs_2450_);
lean_dec_ref_known(v_x_2433_, 2);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2432_, v_ks_2449_, v_vs_2450_, v___x_2451_, v_x_2434_);
lean_dec_ref(v_vs_2450_);
lean_dec_ref(v_ks_2449_);
return v___x_2452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_2453_, lean_object* v_as_2454_, lean_object* v_i_2455_, lean_object* v_stop_2456_, lean_object* v_b_2457_){
_start:
{
size_t v_i_boxed_2458_; size_t v_stop_boxed_2459_; lean_object* v_res_2460_; 
v_i_boxed_2458_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_stop_boxed_2459_ = lean_unbox_usize(v_stop_2456_);
lean_dec(v_stop_2456_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2453_, v_as_2454_, v_i_boxed_2458_, v_stop_boxed_2459_, v_b_2457_);
lean_dec_ref(v_as_2454_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_2461_, lean_object* v_s_2462_, lean_object* v_a_2463_, lean_object* v_b_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2463_);
lean_ctor_set(v___x_2465_, 1, v_b_2464_);
v___x_2466_ = lean_apply_2(v_f_2461_, v___x_2465_, v_s_2462_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
v_a_2475_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2466_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2466_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_2483_, lean_object* v_init_2484_, lean_object* v_f_2485_){
_start:
{
lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v_a_2488_; 
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2486_, 0, v_f_2485_);
lean_inc_ref(v_map_2483_);
v___x_2487_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_2486_, v_map_2483_, v_init_2484_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref(v___x_2487_);
return v_a_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_2489_, lean_object* v_init_2490_, lean_object* v_f_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2489_, v_init_2490_, v_f_2491_);
lean_dec_ref(v_map_2489_);
return v_res_2492_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_2495_, lean_object* v_a_2496_, uint8_t v___x_2497_, lean_object* v_as_x27_2498_, lean_object* v_b_2499_){
_start:
{
if (lean_obj_tag(v_as_x27_2498_) == 0)
{
lean_dec(v_a_2496_);
lean_dec_ref(v_tactics_2495_);
return v_b_2499_;
}
else
{
lean_object* v_head_2500_; lean_object* v_fst_2501_; lean_object* v_info_2502_; lean_object* v_tail_2503_; lean_object* v_collectKinds_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_head_2500_ = lean_ctor_get(v_as_x27_2498_, 0);
v_fst_2501_ = lean_ctor_get(v_head_2500_, 0);
v_info_2502_ = lean_ctor_get(v_fst_2501_, 0);
v_tail_2503_ = lean_ctor_get(v_as_x27_2498_, 1);
v_collectKinds_2504_ = lean_ctor_get(v_info_2502_, 1);
v___x_2505_ = lean_box(v___x_2497_);
lean_inc(v_a_2496_);
lean_inc_ref(v_tactics_2495_);
v___f_2506_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2506_, 0, v_tactics_2495_);
lean_closure_set(v___f_2506_, 1, v_a_2496_);
lean_closure_set(v___f_2506_, 2, v___x_2505_);
v___x_2507_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_2504_);
v___x_2508_ = lean_apply_1(v_collectKinds_2504_, v___x_2507_);
v___x_2509_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_2508_, v_b_2499_, v___f_2506_);
lean_dec_ref(v___x_2508_);
v_as_x27_2498_ = v_tail_2503_;
v_b_2499_ = v___x_2509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_2511_, lean_object* v_a_2512_, lean_object* v___x_2513_, lean_object* v_as_x27_2514_, lean_object* v_b_2515_){
_start:
{
uint8_t v___x_4042__boxed_2516_; lean_object* v_res_2517_; 
v___x_4042__boxed_2516_ = lean_unbox(v___x_2513_);
v_res_2517_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2511_, v_a_2512_, v___x_4042__boxed_2516_, v_as_x27_2514_, v_b_2515_);
lean_dec(v_as_x27_2514_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_2520_, lean_object* v_init_2521_, lean_object* v_x_2522_){
_start:
{
if (lean_obj_tag(v_x_2522_) == 0)
{
lean_object* v_k_2523_; lean_object* v_v_2524_; lean_object* v_l_2525_; lean_object* v_r_2526_; lean_object* v___x_2527_; lean_object* v_a_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_k_2523_ = lean_ctor_get(v_x_2522_, 1);
lean_inc(v_k_2523_);
v_v_2524_ = lean_ctor_get(v_x_2522_, 2);
lean_inc(v_v_2524_);
v_l_2525_ = lean_ctor_get(v_x_2522_, 3);
lean_inc(v_l_2525_);
v_r_2526_ = lean_ctor_get(v_x_2522_, 4);
lean_inc(v_r_2526_);
lean_dec_ref_known(v_x_2522_, 5);
lean_inc_ref(v_tactics_2520_);
v___x_2527_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2520_, v_init_2521_, v_l_2525_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
v___x_2529_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0));
v___x_2530_ = lean_name_eq(v_k_2523_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_dec_ref(v___x_2527_);
lean_inc_ref(v_tactics_2520_);
v___x_2531_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2520_, v_k_2523_, v___x_2530_, v_v_2524_, v_a_2528_);
lean_dec(v_v_2524_);
v_init_2521_ = v___x_2531_;
v_x_2522_ = v_r_2526_;
goto _start;
}
else
{
lean_object* v_a_2533_; 
lean_dec(v_a_2528_);
lean_dec(v_v_2524_);
lean_dec(v_k_2523_);
v_a_2533_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2527_);
v_init_2521_ = v_a_2533_;
v_x_2522_ = v_r_2526_;
goto _start;
}
}
else
{
lean_object* v___x_2535_; 
lean_dec_ref(v_tactics_2520_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_init_2521_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_2536_, lean_object* v_table_2537_, lean_object* v_firsts_2538_){
_start:
{
lean_object* v___x_2539_; lean_object* v_a_2540_; 
v___x_2539_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2536_, v_firsts_2538_, v_table_2537_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2539_);
return v_a_2540_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
uint8_t v___x_2544_; 
v___x_2544_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2542_, v_x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_2545_, v_x_2546_, v_x_2547_);
lean_dec(v_x_2547_);
lean_dec_ref(v_x_2546_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_2550_, lean_object* v_k_2551_, lean_object* v_t_2552_, lean_object* v_hl_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2550_, v_k_2551_, v_t_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_2555_, lean_object* v_00_u03b2_2556_, lean_object* v_map_2557_, lean_object* v_init_2558_, lean_object* v_f_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2557_, v_init_2558_, v_f_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_2561_, lean_object* v_00_u03b2_2562_, lean_object* v_map_2563_, lean_object* v_init_2564_, lean_object* v_f_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_2561_, v_00_u03b2_2562_, v_map_2563_, v_init_2564_, v_f_2565_);
lean_dec_ref(v_map_2563_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_2567_, lean_object* v_a_2568_, uint8_t v___x_2569_, lean_object* v_as_2570_, lean_object* v_as_x27_2571_, lean_object* v_b_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2567_, v_a_2568_, v___x_2569_, v_as_x27_2571_, v_b_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_2575_, lean_object* v_a_2576_, lean_object* v___x_2577_, lean_object* v_as_2578_, lean_object* v_as_x27_2579_, lean_object* v_b_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v___x_4122__boxed_2582_; lean_object* v_res_2583_; 
v___x_4122__boxed_2582_ = lean_unbox(v___x_2577_);
v_res_2583_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2575_, v_a_2576_, v___x_4122__boxed_2582_, v_as_2578_, v_as_x27_2579_, v_b_2580_, v_a_2581_);
lean_dec(v_as_x27_2579_);
lean_dec(v_as_2578_);
return v_res_2583_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_2584_, lean_object* v_x_2585_, size_t v_x_2586_, lean_object* v_x_2587_){
_start:
{
uint8_t v___x_2588_; 
v___x_2588_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2585_, v_x_2586_, v_x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_, lean_object* v_x_2592_){
_start:
{
size_t v_x_4131__boxed_2593_; uint8_t v_res_2594_; lean_object* v_r_2595_; 
v_x_4131__boxed_2593_ = lean_unbox_usize(v_x_2591_);
lean_dec(v_x_2591_);
v_res_2594_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_2589_, v_x_2590_, v_x_4131__boxed_2593_, v_x_2592_);
lean_dec(v_x_2592_);
lean_dec_ref(v_x_2590_);
v_r_2595_ = lean_box(v_res_2594_);
return v_r_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_2596_, lean_object* v_f_2597_, lean_object* v_init_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2597_, v_map_2596_, v_init_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_2600_, lean_object* v_00_u03c3_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_map_2603_, lean_object* v_f_2604_, lean_object* v_init_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2604_, v_map_2603_, v_init_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2607_, lean_object* v_keys_2608_, lean_object* v_vals_2609_, lean_object* v_heq_2610_, lean_object* v_i_2611_, lean_object* v_k_2612_){
_start:
{
uint8_t v___x_2613_; 
v___x_2613_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2608_, v_i_2611_, v_k_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2614_, lean_object* v_keys_2615_, lean_object* v_vals_2616_, lean_object* v_heq_2617_, lean_object* v_i_2618_, lean_object* v_k_2619_){
_start:
{
uint8_t v_res_2620_; lean_object* v_r_2621_; 
v_res_2620_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_2614_, v_keys_2615_, v_vals_2616_, v_heq_2617_, v_i_2618_, v_k_2619_);
lean_dec(v_k_2619_);
lean_dec_ref(v_vals_2616_);
lean_dec_ref(v_keys_2615_);
v_r_2621_ = lean_box(v_res_2620_);
return v_r_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_2622_, lean_object* v_00_u03c3_2623_, lean_object* v_00_u03b1_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_f_2626_, lean_object* v_x_2627_, lean_object* v_x_2628_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2626_, v_x_2627_, v_x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_2630_, lean_object* v_00_u03b2_2631_, lean_object* v_00_u03c3_2632_, lean_object* v_00_u03c3_2633_, lean_object* v_f_2634_, lean_object* v_as_2635_, size_t v_i_2636_, size_t v_stop_2637_, lean_object* v_b_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2634_, v_as_2635_, v_i_2636_, v_stop_2637_, v_b_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_00_u03b2_2641_, lean_object* v_00_u03c3_2642_, lean_object* v_00_u03c3_2643_, lean_object* v_f_2644_, lean_object* v_as_2645_, lean_object* v_i_2646_, lean_object* v_stop_2647_, lean_object* v_b_2648_){
_start:
{
size_t v_i_boxed_2649_; size_t v_stop_boxed_2650_; lean_object* v_res_2651_; 
v_i_boxed_2649_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_stop_boxed_2650_ = lean_unbox_usize(v_stop_2647_);
lean_dec(v_stop_2647_);
v_res_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_2640_, v_00_u03b2_2641_, v_00_u03c3_2642_, v_00_u03c3_2643_, v_f_2644_, v_as_2645_, v_i_boxed_2649_, v_stop_boxed_2650_, v_b_2648_);
lean_dec_ref(v_as_2645_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_2652_, lean_object* v_00_u03c3_2653_, lean_object* v_00_u03b1_2654_, lean_object* v_00_u03b2_2655_, lean_object* v_f_2656_, lean_object* v_keys_2657_, lean_object* v_vals_2658_, lean_object* v_heq_2659_, lean_object* v_i_2660_, lean_object* v_acc_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2656_, v_keys_2657_, v_vals_2658_, v_i_2660_, v_acc_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_2663_, lean_object* v_00_u03c3_2664_, lean_object* v_00_u03b1_2665_, lean_object* v_00_u03b2_2666_, lean_object* v_f_2667_, lean_object* v_keys_2668_, lean_object* v_vals_2669_, lean_object* v_heq_2670_, lean_object* v_i_2671_, lean_object* v_acc_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_2663_, v_00_u03c3_2664_, v_00_u03b1_2665_, v_00_u03b2_2666_, v_f_2667_, v_keys_2668_, v_vals_2669_, v_heq_2670_, v_i_2671_, v_acc_2672_);
lean_dec_ref(v_vals_2669_);
lean_dec_ref(v_keys_2668_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_2674_, lean_object* v_x2_2675_){
_start:
{
lean_object* v_fst_2676_; lean_object* v_snd_2677_; lean_object* v___x_2678_; 
v_fst_2676_ = lean_ctor_get(v_x2_2675_, 0);
lean_inc(v_fst_2676_);
v_snd_2677_ = lean_ctor_get(v_x2_2675_, 1);
lean_inc(v_snd_2677_);
lean_dec_ref(v_x2_2675_);
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2676_, v_snd_2677_, v_x1_2674_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_2698_, lean_object* v_x1_2699_, lean_object* v_x2_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_array_get_size(v_x2_2700_);
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2704_ = lean_nat_dec_lt(v___x_2701_, v___x_2702_);
if (v___x_2704_ == 0)
{
lean_dec_ref(v_x2_2700_);
lean_dec_ref(v___f_2698_);
return v_x1_2699_;
}
else
{
uint8_t v___x_2705_; 
v___x_2705_ = lean_nat_dec_le(v___x_2702_, v___x_2702_);
if (v___x_2705_ == 0)
{
if (v___x_2704_ == 0)
{
lean_dec_ref(v_x2_2700_);
lean_dec_ref(v___f_2698_);
return v_x1_2699_;
}
else
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = lean_usize_of_nat(v___x_2702_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2703_, v___f_2698_, v_x2_2700_, v___x_2706_, v___x_2707_, v_x1_2699_);
return v___x_2708_;
}
}
else
{
size_t v___x_2709_; size_t v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2702_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2703_, v___f_2698_, v_x2_2700_, v___x_2709_, v___x_2710_, v_x1_2699_);
return v___x_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v___x_2717_, lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v_toPure_2720_, lean_object* v___f_2721_, lean_object* v_env_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v_ext_2724_; lean_object* v_toEnvExtension_2725_; lean_object* v_asyncMode_2726_; lean_object* v___x_2727_; lean_object* v_categories_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2723_ = l_Lean_Parser_parserExtension;
v_ext_2724_ = lean_ctor_get(v___x_2723_, 1);
v_toEnvExtension_2725_ = lean_ctor_get(v_ext_2724_, 0);
v_asyncMode_2726_ = lean_ctor_get(v_toEnvExtension_2725_, 2);
lean_inc_ref(v_env_2722_);
v___x_2727_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2715_, v___x_2723_, v_env_2722_, v_asyncMode_2726_);
v_categories_2728_ = lean_ctor_get(v___x_2727_, 2);
lean_inc_ref(v_categories_2728_);
lean_dec(v___x_2727_);
v___x_2729_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2730_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2716_, v___x_2717_, v_categories_2728_, v___x_2729_);
lean_dec_ref(v_categories_2728_);
if (lean_obj_tag(v___x_2730_) == 1)
{
lean_object* v_val_2731_; lean_object* v___y_2733_; lean_object* v___x_2740_; lean_object* v_toEnvExtension_2741_; lean_object* v_exportEntriesFn_2742_; lean_object* v_asyncMode_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v_importedEntries_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v_exported_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v_val_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_val_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2740_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2741_ = lean_ctor_get(v___x_2740_, 0);
v_exportEntriesFn_2742_ = lean_ctor_get(v___x_2740_, 4);
v_asyncMode_2743_ = lean_ctor_get(v_toEnvExtension_2741_, 2);
v___x_2744_ = lean_box(0);
lean_inc_ref_n(v_env_2722_, 2);
v___x_2745_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2718_, v_toEnvExtension_2741_, v_env_2722_, v_asyncMode_2743_, v___x_2744_);
v_importedEntries_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_ref(v_importedEntries_2746_);
lean_dec(v___x_2745_);
v___x_2747_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2719_, v___x_2740_, v_env_2722_, v_asyncMode_2743_, v___x_2744_);
lean_inc_ref(v_exportEntriesFn_2742_);
v___x_2748_ = lean_apply_2(v_exportEntriesFn_2742_, v_env_2722_, v___x_2747_);
v_exported_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_exported_2749_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = lean_box(1);
v___x_2751_ = lean_array_push(v_importedEntries_2746_, v_exported_2749_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_array_get_size(v___x_2751_);
v___x_2754_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2755_ = lean_nat_dec_lt(v___x_2752_, v___x_2753_);
if (v___x_2755_ == 0)
{
lean_dec_ref(v___x_2751_);
lean_dec_ref(v___f_2721_);
v___y_2733_ = v___x_2750_;
goto v___jp_2732_;
}
else
{
uint8_t v___x_2756_; 
v___x_2756_ = lean_nat_dec_le(v___x_2753_, v___x_2753_);
if (v___x_2756_ == 0)
{
if (v___x_2755_ == 0)
{
lean_dec_ref(v___x_2751_);
lean_dec_ref(v___f_2721_);
v___y_2733_ = v___x_2750_;
goto v___jp_2732_;
}
else
{
size_t v___x_2757_; size_t v___x_2758_; lean_object* v___x_2759_; 
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = lean_usize_of_nat(v___x_2753_);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2754_, v___f_2721_, v___x_2751_, v___x_2757_, v___x_2758_, v___x_2750_);
v___y_2733_ = v___x_2759_;
goto v___jp_2732_;
}
}
else
{
size_t v___x_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = lean_usize_of_nat(v___x_2753_);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2754_, v___f_2721_, v___x_2751_, v___x_2760_, v___x_2761_, v___x_2750_);
v___y_2733_ = v___x_2762_;
goto v___jp_2732_;
}
}
v___jp_2732_:
{
lean_object* v_tables_2734_; lean_object* v_leadingTable_2735_; lean_object* v_trailingTable_2736_; lean_object* v_firstTokens_2737_; lean_object* v_firstTokens_2738_; lean_object* v___x_2739_; 
v_tables_2734_ = lean_ctor_get(v_val_2731_, 2);
v_leadingTable_2735_ = lean_ctor_get(v_tables_2734_, 0);
v_trailingTable_2736_ = lean_ctor_get(v_tables_2734_, 2);
lean_inc(v_trailingTable_2736_);
lean_inc(v_leadingTable_2735_);
lean_inc(v_val_2731_);
v_firstTokens_2737_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2731_, v_leadingTable_2735_, v___y_2733_);
v_firstTokens_2738_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2731_, v_trailingTable_2736_, v_firstTokens_2737_);
v___x_2739_ = lean_apply_2(v_toPure_2720_, lean_box(0), v_firstTokens_2738_);
return v___x_2739_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v___x_2730_);
lean_dec_ref(v_env_2722_);
lean_dec_ref(v___f_2721_);
lean_dec(v___x_2719_);
v___x_2763_ = lean_box(1);
v___x_2764_ = lean_apply_2(v_toPure_2720_, lean_box(0), v___x_2763_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_2765_, lean_object* v___x_2766_, lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v_toPure_2770_, lean_object* v___f_2771_, lean_object* v_env_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_2765_, v___x_2766_, v___x_2767_, v___x_2768_, v___x_2769_, v_toPure_2770_, v___f_2771_, v_env_2772_);
lean_dec_ref(v___x_2768_);
lean_dec_ref(v___x_2765_);
return v_res_2773_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_box(1);
v___x_2778_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_2781_, lean_object* v_inst_2782_){
_start:
{
lean_object* v_toApplicative_2783_; lean_object* v_toBind_2784_; lean_object* v_getEnv_2785_; lean_object* v_toPure_2786_; lean_object* v___f_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; 
v_toApplicative_2783_ = lean_ctor_get(v_inst_2781_, 0);
lean_inc_ref(v_toApplicative_2783_);
v_toBind_2784_ = lean_ctor_get(v_inst_2781_, 1);
lean_inc(v_toBind_2784_);
lean_dec_ref(v_inst_2781_);
v_getEnv_2785_ = lean_ctor_get(v_inst_2782_, 0);
lean_inc(v_getEnv_2785_);
lean_dec_ref(v_inst_2782_);
v_toPure_2786_ = lean_ctor_get(v_toApplicative_2783_, 1);
lean_inc(v_toPure_2786_);
lean_dec_ref(v_toApplicative_2783_);
v___f_2787_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_2788_ = lean_box(1);
v___x_2789_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2790_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2791_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_2792_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_2793_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2793_, 0, v___x_2792_);
lean_closure_set(v___f_2793_, 1, v___x_2790_);
lean_closure_set(v___f_2793_, 2, v___x_2791_);
lean_closure_set(v___f_2793_, 3, v___x_2789_);
lean_closure_set(v___f_2793_, 4, v___x_2788_);
lean_closure_set(v___f_2793_, 5, v_toPure_2786_);
lean_closure_set(v___f_2793_, 6, v___f_2787_);
v___x_2794_ = lean_apply_4(v_toBind_2784_, lean_box(0), lean_box(0), v_getEnv_2785_, v___f_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_2795_, lean_object* v_inst_2796_, lean_object* v_inst_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_2796_, v_inst_2797_);
return v___x_2798_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = lean_box(1);
v___x_2802_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_2803_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v___x_2802_);
lean_ctor_set(v___x_2804_, 2, v___x_2801_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_2806_, lean_object* v___y_2807_, lean_object* v_toPure_2808_, lean_object* v_firsts_2809_, lean_object* v_____do__lift_2810_){
_start:
{
lean_object* v___y_2812_; lean_object* v_val_2823_; 
if (lean_obj_tag(v_____do__lift_2810_) == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_2806_);
v___x_2826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_2825_, v_firsts_2809_, v_n_2806_);
if (lean_obj_tag(v___x_2826_) == 0)
{
uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = 1;
lean_inc(v_n_2806_);
v___x_2828_ = l_Lean_Name_toString(v_n_2806_, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
v___y_2812_ = v___x_2829_;
goto v___jp_2811_;
}
else
{
lean_object* v_val_2830_; 
v_val_2830_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2826_, 1);
v_val_2823_ = v_val_2830_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_val_2831_; 
lean_dec(v_firsts_2809_);
v_val_2831_ = lean_ctor_get(v_____do__lift_2810_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v_____do__lift_2810_, 1);
v_val_2823_ = v_val_2831_;
goto v___jp_2822_;
}
v___jp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2813_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_2814_ = l_Lean_Expr_const___override(v_n_2806_, v___y_2807_);
v___x_2815_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_2816_ = lean_box(0);
v___x_2817_ = 0;
v___x_2818_ = l_Lean_MessageData_withExprHover(v___y_2812_, v___x_2814_, v___x_2815_, v___x_2816_, v___x_2816_, v___x_2816_, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2813_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v___x_2813_);
v___x_2821_ = lean_apply_2(v_toPure_2808_, lean_box(0), v___x_2820_);
return v___x_2821_;
}
v___jp_2822_:
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_val_2823_);
v___y_2812_ = v___x_2824_;
goto v___jp_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_2832_, lean_object* v_toPure_2833_, lean_object* v_firsts_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_toBind_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v___f_2840_, lean_object* v_env_2841_){
_start:
{
lean_object* v___y_2843_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = l_Lean_Environment_constants(v_env_2841_);
lean_inc(v_n_2832_);
v___x_2848_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_2838_, v___x_2839_, v___x_2847_, v_n_2832_);
lean_dec_ref(v___x_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v___f_2840_);
v___x_2849_ = lean_box(0);
v___y_2843_ = v___x_2849_;
goto v___jp_2842_;
}
else
{
lean_object* v_val_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_val_2850_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_val_2850_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2851_ = l_Lean_ConstantInfo_levelParams(v_val_2850_);
lean_dec(v_val_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = l_List_mapTR_loop___redArg(v___f_2840_, v___x_2851_, v___x_2852_);
v___y_2843_ = v___x_2853_;
goto v___jp_2842_;
}
v___jp_2842_:
{
lean_object* v___f_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_inc(v_n_2832_);
v___f_2844_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2844_, 0, v_n_2832_);
lean_closure_set(v___f_2844_, 1, v___y_2843_);
lean_closure_set(v___f_2844_, 2, v_toPure_2833_);
lean_closure_set(v___f_2844_, 3, v_firsts_2834_);
v___x_2845_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_2835_, v_inst_2836_, v_n_2832_);
v___x_2846_ = lean_apply_4(v_toBind_2837_, lean_box(0), lean_box(0), v___x_2845_, v___f_2844_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_firsts_2857_, lean_object* v_n_2858_){
_start:
{
lean_object* v_toApplicative_2859_; lean_object* v_toBind_2860_; lean_object* v_getEnv_2861_; lean_object* v_toPure_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___f_2866_; lean_object* v___x_2867_; 
v_toApplicative_2859_ = lean_ctor_get(v_inst_2855_, 0);
v_toBind_2860_ = lean_ctor_get(v_inst_2855_, 1);
lean_inc_n(v_toBind_2860_, 2);
v_getEnv_2861_ = lean_ctor_get(v_inst_2856_, 0);
lean_inc(v_getEnv_2861_);
v_toPure_2862_ = lean_ctor_get(v_toApplicative_2859_, 1);
lean_inc(v_toPure_2862_);
v___f_2863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_2864_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2865_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_2866_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_2866_, 0, v_n_2858_);
lean_closure_set(v___f_2866_, 1, v_toPure_2862_);
lean_closure_set(v___f_2866_, 2, v_firsts_2857_);
lean_closure_set(v___f_2866_, 3, v_inst_2855_);
lean_closure_set(v___f_2866_, 4, v_inst_2856_);
lean_closure_set(v___f_2866_, 5, v_toBind_2860_);
lean_closure_set(v___f_2866_, 6, v___x_2864_);
lean_closure_set(v___f_2866_, 7, v___x_2865_);
lean_closure_set(v___f_2866_, 8, v___f_2863_);
v___x_2867_ = lean_apply_4(v_toBind_2860_, lean_box(0), lean_box(0), v_getEnv_2861_, v___f_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_firsts_2871_, lean_object* v_n_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_2869_, v_inst_2870_, v_firsts_2871_, v_n_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_2879_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_2883_);
lean_dec_ref(v_s_2883_);
return v_res_2884_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_2885_, lean_object* v_x1_2886_, lean_object* v_x2_2887_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2888_ = l_Lean_Name_toString(v_x1_2886_, v___x_2885_);
v___x_2889_ = l_Lean_Name_toString(v_x2_2887_, v___x_2885_);
v___x_2890_ = lean_string_dec_lt(v___x_2888_, v___x_2889_);
lean_dec_ref(v___x_2889_);
lean_dec_ref(v___x_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_2891_, lean_object* v_x1_2892_, lean_object* v_x2_2893_){
_start:
{
uint8_t v___x_16939__boxed_2894_; uint8_t v_res_2895_; lean_object* v_r_2896_; 
v___x_16939__boxed_2894_ = lean_unbox(v___x_2891_);
v_res_2895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16939__boxed_2894_, v_x1_2892_, v_x2_2893_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_2897_, lean_object* v_pivot_2898_, lean_object* v_as_2899_, lean_object* v_i_2900_, lean_object* v_k_2901_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_nat_dec_lt(v_k_2901_, v_hi_2897_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v_k_2901_);
lean_dec(v_pivot_2898_);
v___x_2903_ = lean_array_fswap(v_as_2899_, v_i_2900_, v_hi_2897_);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v_i_2900_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
return v___x_2904_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2905_ = lean_array_fget_borrowed(v_as_2899_, v_k_2901_);
lean_inc(v___x_2905_);
v___x_2906_ = l_Lean_Name_toString(v___x_2905_, v___x_2902_);
lean_inc(v_pivot_2898_);
v___x_2907_ = l_Lean_Name_toString(v_pivot_2898_, v___x_2902_);
v___x_2908_ = lean_string_dec_lt(v___x_2906_, v___x_2907_);
lean_dec_ref(v___x_2907_);
lean_dec_ref(v___x_2906_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = lean_nat_add(v_k_2901_, v___x_2909_);
lean_dec(v_k_2901_);
v_k_2901_ = v___x_2910_;
goto _start;
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2912_ = lean_array_fswap(v_as_2899_, v_i_2900_, v_k_2901_);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = lean_nat_add(v_i_2900_, v___x_2913_);
lean_dec(v_i_2900_);
v___x_2915_ = lean_nat_add(v_k_2901_, v___x_2913_);
lean_dec(v_k_2901_);
v_as_2899_ = v___x_2912_;
v_i_2900_ = v___x_2914_;
v_k_2901_ = v___x_2915_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_2917_, lean_object* v_pivot_2918_, lean_object* v_as_2919_, lean_object* v_i_2920_, lean_object* v_k_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2917_, v_pivot_2918_, v_as_2919_, v_i_2920_, v_k_2921_);
lean_dec(v_hi_2917_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_2923_, lean_object* v_as_2924_, lean_object* v_lo_2925_, lean_object* v_hi_2926_){
_start:
{
lean_object* v___y_2928_; uint8_t v___x_2938_; 
v___x_2938_ = lean_nat_dec_lt(v_lo_2925_, v_hi_2926_);
if (v___x_2938_ == 0)
{
lean_dec(v_lo_2925_);
return v_as_2924_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_mid_2941_; lean_object* v___y_2943_; lean_object* v___y_2949_; lean_object* v___x_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2939_ = lean_nat_add(v_lo_2925_, v_hi_2926_);
v___x_2940_ = lean_unsigned_to_nat(1u);
v_mid_2941_ = lean_nat_shiftr(v___x_2939_, v___x_2940_);
lean_dec(v___x_2939_);
v___x_2954_ = lean_array_fget_borrowed(v_as_2924_, v_mid_2941_);
v___x_2955_ = lean_array_fget_borrowed(v_as_2924_, v_lo_2925_);
lean_inc(v___x_2955_);
lean_inc(v___x_2954_);
v___x_2956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2938_, v___x_2954_, v___x_2955_);
if (v___x_2956_ == 0)
{
v___y_2949_ = v_as_2924_;
goto v___jp_2948_;
}
else
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_array_fswap(v_as_2924_, v_lo_2925_, v_mid_2941_);
v___y_2949_ = v___x_2957_;
goto v___jp_2948_;
}
v___jp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2944_ = lean_array_fget_borrowed(v___y_2943_, v_mid_2941_);
v___x_2945_ = lean_array_fget_borrowed(v___y_2943_, v_hi_2926_);
lean_inc(v___x_2945_);
lean_inc(v___x_2944_);
v___x_2946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2938_, v___x_2944_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec(v_mid_2941_);
v___y_2928_ = v___y_2943_;
goto v___jp_2927_;
}
else
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_array_fswap(v___y_2943_, v_mid_2941_, v_hi_2926_);
lean_dec(v_mid_2941_);
v___y_2928_ = v___x_2947_;
goto v___jp_2927_;
}
}
v___jp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = lean_array_fget_borrowed(v___y_2949_, v_hi_2926_);
v___x_2951_ = lean_array_fget_borrowed(v___y_2949_, v_lo_2925_);
lean_inc(v___x_2951_);
lean_inc(v___x_2950_);
v___x_2952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2938_, v___x_2950_, v___x_2951_);
if (v___x_2952_ == 0)
{
v___y_2943_ = v___y_2949_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_array_fswap(v___y_2949_, v_lo_2925_, v_hi_2926_);
v___y_2943_ = v___x_2953_;
goto v___jp_2942_;
}
}
}
v___jp_2927_:
{
lean_object* v_pivot_2929_; lean_object* v___x_2930_; lean_object* v_fst_2931_; lean_object* v_snd_2932_; uint8_t v___x_2933_; 
v_pivot_2929_ = lean_array_fget(v___y_2928_, v_hi_2926_);
lean_inc_n(v_lo_2925_, 2);
v___x_2930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2926_, v_pivot_2929_, v___y_2928_, v_lo_2925_, v_lo_2925_);
v_fst_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_fst_2931_);
v_snd_2932_ = lean_ctor_get(v___x_2930_, 1);
lean_inc(v_snd_2932_);
lean_dec_ref(v___x_2930_);
v___x_2933_ = lean_nat_dec_le(v_hi_2926_, v_fst_2931_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2923_, v_snd_2932_, v_lo_2925_, v_fst_2931_);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_nat_add(v_fst_2931_, v___x_2935_);
lean_dec(v_fst_2931_);
v_as_2924_ = v___x_2934_;
v_lo_2925_ = v___x_2936_;
goto _start;
}
else
{
lean_dec(v_fst_2931_);
lean_dec(v_lo_2925_);
return v_snd_2932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_2958_, lean_object* v_as_2959_, lean_object* v_lo_2960_, lean_object* v_hi_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2958_, v_as_2959_, v_lo_2960_, v_hi_2961_);
lean_dec(v_hi_2961_);
lean_dec(v_n_2958_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_2963_, lean_object* v_x_2964_){
_start:
{
if (lean_obj_tag(v_x_2964_) == 0)
{
lean_object* v_k_2965_; lean_object* v_l_2966_; lean_object* v_r_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_k_2965_ = lean_ctor_get(v_x_2964_, 1);
lean_inc(v_k_2965_);
v_l_2966_ = lean_ctor_get(v_x_2964_, 3);
lean_inc(v_l_2966_);
v_r_2967_ = lean_ctor_get(v_x_2964_, 4);
lean_inc(v_r_2967_);
lean_dec_ref_known(v_x_2964_, 5);
v___x_2968_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2963_, v_l_2966_);
v___x_2969_ = lean_array_push(v___x_2968_, v_k_2965_);
v_init_2963_ = v___x_2969_;
v_x_2964_ = v_r_2967_;
goto _start;
}
else
{
return v_init_2963_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
if (lean_obj_tag(v_a_2971_) == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = l_List_reverse___redArg(v_a_2972_);
return v___x_2973_;
}
else
{
lean_object* v_head_2974_; lean_object* v_tail_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2984_; 
v_head_2974_ = lean_ctor_get(v_a_2971_, 0);
v_tail_2975_ = lean_ctor_get(v_a_2971_, 1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_a_2971_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2977_ = v_a_2971_;
v_isShared_2978_ = v_isSharedCheck_2984_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_tail_2975_);
lean_inc(v_head_2974_);
lean_dec(v_a_2971_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2984_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2979_ = l_Lean_Level_param___override(v_head_2974_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v_a_2972_);
lean_ctor_set(v___x_2977_, 0, v___x_2979_);
v___x_2981_ = v___x_2977_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_a_2972_);
v___x_2981_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
v_a_2971_ = v_tail_2975_;
v_a_2972_ = v___x_2981_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_2985_, lean_object* v_x2_2986_){
_start:
{
lean_object* v_fst_2987_; lean_object* v_fst_2988_; uint8_t v___x_2989_; 
v_fst_2987_ = lean_ctor_get(v_x1_2985_, 0);
v_fst_2988_ = lean_ctor_get(v_x2_2986_, 0);
v___x_2989_ = l_Lean_Name_quickLt(v_fst_2987_, v_fst_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_2990_, lean_object* v_x2_2991_){
_start:
{
uint8_t v_res_2992_; lean_object* v_r_2993_; 
v_res_2992_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_2990_, v_x2_2991_);
lean_dec_ref(v_x2_2991_);
lean_dec_ref(v_x1_2990_);
v_r_2993_ = lean_box(v_res_2992_);
return v_r_2993_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_2994_, lean_object* v_k_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_m_3000_; lean_object* v_a_3001_; uint8_t v___x_3002_; 
v___x_2998_ = lean_nat_add(v_x_2996_, v_x_2997_);
v___x_2999_ = lean_unsigned_to_nat(1u);
v_m_3000_ = lean_nat_shiftr(v___x_2998_, v___x_2999_);
lean_dec(v___x_2998_);
v_a_3001_ = lean_array_fget_borrowed(v_as_2994_, v_m_3000_);
v___x_3002_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_3001_, v_k_2995_);
if (v___x_3002_ == 0)
{
uint8_t v___x_3003_; 
lean_dec(v_x_2997_);
v___x_3003_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_2995_, v_a_3001_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
lean_dec(v_m_3000_);
lean_dec(v_x_2996_);
lean_inc(v_a_3001_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_a_3001_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; uint8_t v___y_3009_; 
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = lean_nat_dec_eq(v_m_3000_, v___x_3005_);
v___x_3007_ = lean_nat_sub(v_m_3000_, v___x_2999_);
lean_dec(v_m_3000_);
if (v___x_3006_ == 0)
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_nat_dec_lt(v___x_3007_, v_x_2996_);
v___y_3009_ = v___x_3012_;
goto v___jp_3008_;
}
else
{
v___y_3009_ = v___x_3006_;
goto v___jp_3008_;
}
v___jp_3008_:
{
if (v___y_3009_ == 0)
{
v_x_2997_ = v___x_3007_;
goto _start;
}
else
{
lean_object* v___x_3011_; 
lean_dec(v___x_3007_);
lean_dec(v_x_2996_);
v___x_3011_ = lean_box(0);
return v___x_3011_;
}
}
}
}
else
{
lean_object* v___x_3013_; uint8_t v___x_3014_; 
lean_dec(v_x_2996_);
v___x_3013_ = lean_nat_add(v_m_3000_, v___x_2999_);
lean_dec(v_m_3000_);
v___x_3014_ = lean_nat_dec_le(v___x_3013_, v_x_2997_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
lean_dec(v___x_3013_);
lean_dec(v_x_2997_);
v___x_3015_ = lean_box(0);
return v___x_3015_;
}
else
{
v_x_2996_ = v___x_3013_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_3017_, lean_object* v_k_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3017_, v_k_3018_, v_x_3019_, v_x_3020_);
lean_dec_ref(v_k_3018_);
lean_dec_ref(v_as_3017_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_env_3030_; lean_object* v___x_3031_; 
v___x_3025_ = lean_box(1);
v___x_3026_ = lean_st_ref_get(v___y_3023_);
v_env_3030_ = lean_ctor_get(v___x_3026_, 0);
lean_inc_ref(v_env_3030_);
lean_dec(v___x_3026_);
v___x_3031_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3030_, v_tac_3022_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3032_; lean_object* v_toEnvExtension_3033_; lean_object* v_asyncMode_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3032_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3033_ = lean_ctor_get(v___x_3032_, 0);
v_asyncMode_3034_ = lean_ctor_get(v_toEnvExtension_3033_, 2);
v___x_3035_ = lean_box(0);
v___x_3036_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3025_, v___x_3032_, v_env_3030_, v_asyncMode_3034_, v___x_3035_);
v___x_3037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3036_, v_tac_3022_);
lean_dec(v_tac_3022_);
lean_dec(v___x_3036_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
else
{
lean_object* v_val_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3067_; 
v_val_3039_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3041_ = v___x_3031_;
v_isShared_3042_ = v_isSharedCheck_3067_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_val_3039_);
lean_dec(v___x_3031_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3067_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; uint8_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3043_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3044_ = 0;
v___x_3045_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3025_, v___x_3043_, v_env_3030_, v_val_3039_, v___x_3044_);
lean_dec(v_val_3039_);
lean_dec_ref(v_env_3030_);
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = lean_array_get_size(v___x_3045_);
v___x_3048_ = lean_nat_dec_lt(v___x_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_dec_ref(v___x_3045_);
lean_del_object(v___x_3041_);
lean_dec(v_tac_3022_);
goto v___jp_3027_;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3049_ = lean_unsigned_to_nat(1u);
v___x_3050_ = lean_nat_sub(v___x_3047_, v___x_3049_);
v___x_3051_ = lean_nat_dec_le(v___x_3046_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_dec(v___x_3050_);
lean_dec_ref(v___x_3045_);
lean_del_object(v___x_3041_);
lean_dec(v_tac_3022_);
goto v___jp_3027_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v_tac_3022_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_3045_, v___x_3053_, v___x_3046_, v___x_3050_);
lean_dec_ref_known(v___x_3053_, 2);
lean_dec_ref(v___x_3045_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_del_object(v___x_3041_);
goto v___jp_3027_;
}
else
{
lean_object* v_val_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3066_; 
v_val_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3066_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_val_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3066_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v_snd_3059_; lean_object* v___x_3061_; 
v_snd_3059_ = lean_ctor_get(v_val_3055_, 1);
lean_inc(v_snd_3059_);
lean_dec(v_val_3055_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v_snd_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_snd_3059_);
v___x_3061_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3063_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3061_);
v___x_3063_ = v___x_3041_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
}
}
v___jp_3027_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3068_, v___y_3069_);
lean_dec(v___y_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_3072_, lean_object* v_k_3073_){
_start:
{
if (lean_obj_tag(v_t_3072_) == 0)
{
lean_object* v_k_3074_; lean_object* v_v_3075_; lean_object* v_l_3076_; lean_object* v_r_3077_; uint8_t v___x_3078_; 
v_k_3074_ = lean_ctor_get(v_t_3072_, 1);
v_v_3075_ = lean_ctor_get(v_t_3072_, 2);
v_l_3076_ = lean_ctor_get(v_t_3072_, 3);
v_r_3077_ = lean_ctor_get(v_t_3072_, 4);
v___x_3078_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3073_, v_k_3074_);
switch(v___x_3078_)
{
case 0:
{
v_t_3072_ = v_l_3076_;
goto _start;
}
case 1:
{
lean_object* v___x_3080_; 
lean_inc(v_v_3075_);
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_v_3075_);
return v___x_3080_;
}
default: 
{
v_t_3072_ = v_r_3077_;
goto _start;
}
}
}
else
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_3083_, lean_object* v_k_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3083_, v_k_3084_);
lean_dec(v_k_3084_);
lean_dec(v_t_3083_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_3086_, lean_object* v_x_3087_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_box(0);
return v___x_3088_;
}
else
{
lean_object* v_key_3089_; lean_object* v_value_3090_; lean_object* v_tail_3091_; uint8_t v___x_3092_; 
v_key_3089_ = lean_ctor_get(v_x_3087_, 0);
v_value_3090_ = lean_ctor_get(v_x_3087_, 1);
v_tail_3091_ = lean_ctor_get(v_x_3087_, 2);
v___x_3092_ = lean_name_eq(v_key_3089_, v_a_3086_);
if (v___x_3092_ == 0)
{
v_x_3087_ = v_tail_3091_;
goto _start;
}
else
{
lean_object* v___x_3094_; 
lean_inc(v_value_3090_);
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_value_3090_);
return v___x_3094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_3095_, lean_object* v_x_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3095_, v_x_3096_);
lean_dec(v_x_3096_);
lean_dec(v_a_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_buckets_3100_; lean_object* v___x_3101_; uint64_t v___y_3103_; 
v_buckets_3100_ = lean_ctor_get(v_m_3098_, 1);
v___x_3101_ = lean_array_get_size(v_buckets_3100_);
if (lean_obj_tag(v_a_3099_) == 0)
{
uint64_t v___x_3117_; 
v___x_3117_ = 1723ULL;
v___y_3103_ = v___x_3117_;
goto v___jp_3102_;
}
else
{
uint64_t v_hash_3118_; 
v_hash_3118_ = lean_ctor_get_uint64(v_a_3099_, sizeof(void*)*2);
v___y_3103_ = v_hash_3118_;
goto v___jp_3102_;
}
v___jp_3102_:
{
uint64_t v___x_3104_; uint64_t v___x_3105_; uint64_t v_fold_3106_; uint64_t v___x_3107_; uint64_t v___x_3108_; uint64_t v___x_3109_; size_t v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; size_t v___x_3113_; size_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3104_ = 32ULL;
v___x_3105_ = lean_uint64_shift_right(v___y_3103_, v___x_3104_);
v_fold_3106_ = lean_uint64_xor(v___y_3103_, v___x_3105_);
v___x_3107_ = 16ULL;
v___x_3108_ = lean_uint64_shift_right(v_fold_3106_, v___x_3107_);
v___x_3109_ = lean_uint64_xor(v_fold_3106_, v___x_3108_);
v___x_3110_ = lean_uint64_to_usize(v___x_3109_);
v___x_3111_ = lean_usize_of_nat(v___x_3101_);
v___x_3112_ = ((size_t)1ULL);
v___x_3113_ = lean_usize_sub(v___x_3111_, v___x_3112_);
v___x_3114_ = lean_usize_land(v___x_3110_, v___x_3113_);
v___x_3115_ = lean_array_uget_borrowed(v_buckets_3100_, v___x_3114_);
v___x_3116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3099_, v___x_3115_);
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3119_, v_a_3120_);
lean_dec(v_a_3120_);
lean_dec_ref(v_m_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_3122_, lean_object* v_vals_3123_, lean_object* v_i_3124_, lean_object* v_k_3125_){
_start:
{
lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = lean_array_get_size(v_keys_3122_);
v___x_3127_ = lean_nat_dec_lt(v_i_3124_, v___x_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
lean_dec(v_i_3124_);
v___x_3128_ = lean_box(0);
return v___x_3128_;
}
else
{
lean_object* v_k_x27_3129_; uint8_t v___x_3130_; 
v_k_x27_3129_ = lean_array_fget_borrowed(v_keys_3122_, v_i_3124_);
v___x_3130_ = lean_name_eq(v_k_3125_, v_k_x27_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_unsigned_to_nat(1u);
v___x_3132_ = lean_nat_add(v_i_3124_, v___x_3131_);
lean_dec(v_i_3124_);
v_i_3124_ = v___x_3132_;
goto _start;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_array_fget_borrowed(v_vals_3123_, v_i_3124_);
lean_dec(v_i_3124_);
lean_inc(v___x_3134_);
v___x_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_3136_, lean_object* v_vals_3137_, lean_object* v_i_3138_, lean_object* v_k_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3136_, v_vals_3137_, v_i_3138_, v_k_3139_);
lean_dec(v_k_3139_);
lean_dec_ref(v_vals_3137_);
lean_dec_ref(v_keys_3136_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3141_, size_t v_x_3142_, lean_object* v_x_3143_){
_start:
{
if (lean_obj_tag(v_x_3141_) == 0)
{
lean_object* v_es_3144_; lean_object* v___x_3145_; size_t v___x_3146_; size_t v___x_3147_; lean_object* v_j_3148_; lean_object* v___x_3149_; 
v_es_3144_ = lean_ctor_get(v_x_3141_, 0);
v___x_3145_ = lean_box(2);
v___x_3146_ = ((size_t)31ULL);
v___x_3147_ = lean_usize_land(v_x_3142_, v___x_3146_);
v_j_3148_ = lean_usize_to_nat(v___x_3147_);
v___x_3149_ = lean_array_get_borrowed(v___x_3145_, v_es_3144_, v_j_3148_);
lean_dec(v_j_3148_);
switch(lean_obj_tag(v___x_3149_))
{
case 0:
{
lean_object* v_key_3150_; lean_object* v_val_3151_; uint8_t v___x_3152_; 
v_key_3150_ = lean_ctor_get(v___x_3149_, 0);
v_val_3151_ = lean_ctor_get(v___x_3149_, 1);
v___x_3152_ = lean_name_eq(v_x_3143_, v_key_3150_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_box(0);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; 
lean_inc(v_val_3151_);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v_val_3151_);
return v___x_3154_;
}
}
case 1:
{
lean_object* v_node_3155_; size_t v___x_3156_; size_t v___x_3157_; 
v_node_3155_ = lean_ctor_get(v___x_3149_, 0);
v___x_3156_ = ((size_t)5ULL);
v___x_3157_ = lean_usize_shift_right(v_x_3142_, v___x_3156_);
v_x_3141_ = v_node_3155_;
v_x_3142_ = v___x_3157_;
goto _start;
}
default: 
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_box(0);
return v___x_3159_;
}
}
}
else
{
lean_object* v_ks_3160_; lean_object* v_vs_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_ks_3160_ = lean_ctor_get(v_x_3141_, 0);
v_vs_3161_ = lean_ctor_get(v_x_3141_, 1);
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_3160_, v_vs_3161_, v___x_3162_, v_x_3143_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_3164_, lean_object* v_x_3165_, lean_object* v_x_3166_){
_start:
{
size_t v_x_17312__boxed_3167_; lean_object* v_res_3168_; 
v_x_17312__boxed_3167_ = lean_unbox_usize(v_x_3165_);
lean_dec(v_x_3165_);
v_res_3168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3164_, v_x_17312__boxed_3167_, v_x_3166_);
lean_dec(v_x_3166_);
lean_dec_ref(v_x_3164_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_3169_, lean_object* v_x_3170_){
_start:
{
uint64_t v___y_3172_; 
if (lean_obj_tag(v_x_3170_) == 0)
{
uint64_t v___x_3175_; 
v___x_3175_ = 1723ULL;
v___y_3172_ = v___x_3175_;
goto v___jp_3171_;
}
else
{
uint64_t v_hash_3176_; 
v_hash_3176_ = lean_ctor_get_uint64(v_x_3170_, sizeof(void*)*2);
v___y_3172_ = v_hash_3176_;
goto v___jp_3171_;
}
v___jp_3171_:
{
size_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_uint64_to_usize(v___y_3172_);
v___x_3174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3169_, v___x_3173_, v_x_3170_);
return v___x_3174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_3177_, lean_object* v_x_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3177_, v_x_3178_);
lean_dec(v_x_3178_);
lean_dec_ref(v_x_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
uint8_t v_stage_u2081_3182_; 
v_stage_u2081_3182_ = lean_ctor_get_uint8(v_x_3180_, sizeof(void*)*2);
if (v_stage_u2081_3182_ == 0)
{
lean_object* v_map_u2081_3183_; lean_object* v_map_u2082_3184_; lean_object* v___x_3185_; 
v_map_u2081_3183_ = lean_ctor_get(v_x_3180_, 0);
v_map_u2082_3184_ = lean_ctor_get(v_x_3180_, 1);
v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3183_, v_x_3181_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_3184_, v_x_3181_);
return v___x_3186_;
}
else
{
return v___x_3185_;
}
}
else
{
lean_object* v_map_u2081_3187_; lean_object* v___x_3188_; 
v_map_u2081_3187_ = lean_ctor_get(v_x_3180_, 0);
v___x_3188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3187_, v_x_3181_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3189_, v_x_3190_);
lean_dec(v_x_3190_);
lean_dec_ref(v_x_3189_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_3192_, lean_object* v_n_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3212_; lean_object* v_val_3213_; lean_object* v___x_3215_; lean_object* v___y_3217_; lean_object* v_env_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3215_ = lean_st_ref_get(v___y_3195_);
v_env_3232_ = lean_ctor_get(v___x_3215_, 0);
lean_inc_ref(v_env_3232_);
lean_dec(v___x_3215_);
v___x_3233_ = l_Lean_Environment_constants(v_env_3232_);
v___x_3234_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_3233_, v_n_3193_);
lean_dec_ref(v___x_3233_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_box(0);
v___y_3217_ = v___x_3235_;
goto v___jp_3216_;
}
else
{
lean_object* v_val_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_val_3236_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3237_ = l_Lean_ConstantInfo_levelParams(v_val_3236_);
lean_dec(v_val_3236_);
v___x_3238_ = lean_box(0);
v___x_3239_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_3237_, v___x_3238_);
v___y_3217_ = v___x_3239_;
goto v___jp_3216_;
}
v___jp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3200_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_3201_ = l_Lean_Expr_const___override(v_n_3193_, v___y_3198_);
v___x_3202_ = lean_unsigned_to_nat(32u);
v___x_3203_ = lean_mk_empty_array_with_capacity(v___x_3202_);
lean_dec_ref(v___x_3203_);
v___x_3204_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3205_ = lean_box(0);
v___x_3206_ = 0;
v___x_3207_ = l_Lean_MessageData_withExprHover(v___y_3199_, v___x_3201_, v___x_3204_, v___x_3205_, v___x_3205_, v___x_3205_, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3200_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3200_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
v___jp_3211_:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_val_3213_);
v___y_3198_ = v___y_3212_;
v___y_3199_ = v___x_3214_;
goto v___jp_3197_;
}
v___jp_3216_:
{
lean_object* v___x_3218_; lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3231_; 
lean_inc(v_n_3193_);
v___x_3218_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_3193_, v___y_3195_);
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3231_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3231_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
if (lean_obj_tag(v_a_3219_) == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_3192_, v_n_3193_);
if (lean_obj_tag(v___x_3223_) == 0)
{
uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3224_ = 1;
lean_inc(v_n_3193_);
v___x_3225_ = l_Lean_Name_toString(v_n_3193_, v___x_3224_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 3);
lean_ctor_set(v___x_3221_, 0, v___x_3225_);
v___x_3227_ = v___x_3221_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
v___y_3198_ = v___y_3217_;
v___y_3199_ = v___x_3227_;
goto v___jp_3197_;
}
}
else
{
lean_object* v_val_3229_; 
lean_del_object(v___x_3221_);
v_val_3229_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3223_, 1);
v___y_3212_ = v___y_3217_;
v_val_3213_ = v_val_3229_;
goto v___jp_3211_;
}
}
else
{
lean_object* v_val_3230_; 
lean_del_object(v___x_3221_);
v_val_3230_ = lean_ctor_get(v_a_3219_, 0);
lean_inc(v_val_3230_);
lean_dec_ref_known(v_a_3219_, 1);
v___y_3212_ = v___y_3217_;
v_val_3213_ = v_val_3230_;
goto v___jp_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_3240_, lean_object* v_n_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3240_, v_n_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v_firsts_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_3246_, lean_object* v_x_3247_, lean_object* v_x_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
if (lean_obj_tag(v_x_3247_) == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = l_List_reverse___redArg(v_x_3248_);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
else
{
lean_object* v_head_3254_; lean_object* v_tail_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3273_; 
v_head_3254_ = lean_ctor_get(v_x_3247_, 0);
v_tail_3255_ = lean_ctor_get(v_x_3247_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_x_3247_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3257_ = v_x_3247_;
v_isShared_3258_ = v_isSharedCheck_3273_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_tail_3255_);
lean_inc(v_head_3254_);
lean_dec(v_x_3247_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3273_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_3246_, v_head_3254_, v___y_3249_, v___y_3250_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 1, v_x_3248_);
lean_ctor_set(v___x_3257_, 0, v_a_3260_);
v___x_3262_ = v___x_3257_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3260_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_x_3248_);
v___x_3262_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
v_x_3247_ = v_tail_3255_;
v_x_3248_ = v___x_3262_;
goto _start;
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_del_object(v___x_3257_);
lean_dec(v_tail_3255_);
lean_dec(v_x_3248_);
v_a_3265_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3259_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3259_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3274_, v_x_3275_, v_x_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v_a_3274_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_3281_, lean_object* v___x_3282_, lean_object* v___x_3283_, lean_object* v_a_3284_, lean_object* v_b_3285_){
_start:
{
lean_object* v_it_3287_; lean_object* v_startInclusive_3288_; lean_object* v_endExclusive_3289_; 
if (lean_obj_tag(v_a_3284_) == 0)
{
lean_object* v_currPos_3294_; lean_object* v_searcher_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3318_; 
v_currPos_3294_ = lean_ctor_get(v_a_3284_, 0);
v_searcher_3295_ = lean_ctor_get(v_a_3284_, 1);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3297_ = v_a_3284_;
v_isShared_3298_ = v_isSharedCheck_3318_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_searcher_3295_);
lean_inc(v_currPos_3294_);
lean_dec(v_a_3284_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3318_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint8_t v_decide_3299_; 
v_decide_3299_ = lean_nat_dec_eq(v_searcher_3295_, v___x_3283_);
if (v_decide_3299_ == 0)
{
uint32_t v___x_3300_; uint32_t v___x_3301_; uint8_t v___x_3302_; 
v___x_3300_ = 10;
v___x_3301_ = lean_string_utf8_get_fast(v_val_3281_, v_searcher_3295_);
v___x_3302_ = lean_uint32_dec_eq(v___x_3301_, v___x_3300_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = lean_string_utf8_next_fast(v_val_3281_, v_searcher_3295_);
lean_dec(v_searcher_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3303_);
v___x_3305_ = v___x_3297_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_currPos_3294_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
v_a_3284_ = v___x_3305_;
goto _start;
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_slice_3311_; lean_object* v_nextIt_3313_; 
v___x_3308_ = lean_string_utf8_next_fast(v_val_3281_, v_searcher_3295_);
v___x_3309_ = lean_nat_sub(v___x_3308_, v_searcher_3295_);
v___x_3310_ = lean_nat_add(v_searcher_3295_, v___x_3309_);
lean_dec(v___x_3309_);
v_slice_3311_ = l_String_Slice_subslice_x21(v___x_3282_, v_currPos_3294_, v_searcher_3295_);
lean_inc(v___x_3310_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3310_);
lean_ctor_set(v___x_3297_, 0, v___x_3310_);
v_nextIt_3313_ = v___x_3297_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3310_);
v_nextIt_3313_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v_startInclusive_3314_; lean_object* v_endExclusive_3315_; 
v_startInclusive_3314_ = lean_ctor_get(v_slice_3311_, 0);
lean_inc(v_startInclusive_3314_);
v_endExclusive_3315_ = lean_ctor_get(v_slice_3311_, 1);
lean_inc(v_endExclusive_3315_);
lean_dec_ref(v_slice_3311_);
v_it_3287_ = v_nextIt_3313_;
v_startInclusive_3288_ = v_startInclusive_3314_;
v_endExclusive_3289_ = v_endExclusive_3315_;
goto v___jp_3286_;
}
}
}
else
{
lean_object* v___x_3317_; 
lean_del_object(v___x_3297_);
lean_dec(v_searcher_3295_);
v___x_3317_ = lean_box(1);
lean_inc(v___x_3283_);
v_it_3287_ = v___x_3317_;
v_startInclusive_3288_ = v_currPos_3294_;
v_endExclusive_3289_ = v___x_3283_;
goto v___jp_3286_;
}
}
}
else
{
lean_dec(v___x_3283_);
return v_b_3285_;
}
v___jp_3286_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = lean_string_utf8_extract_fast(v_val_3281_, v_startInclusive_3288_, v_endExclusive_3289_);
lean_dec(v_endExclusive_3289_);
lean_dec(v_startInclusive_3288_);
v___x_3291_ = l_Lean_stringToMessageData(v___x_3290_);
v___x_3292_ = lean_array_push(v_b_3285_, v___x_3291_);
v_a_3284_ = v_it_3287_;
v_b_3285_ = v___x_3292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3319_, v___x_3320_, v___x_3321_, v_a_3322_, v_b_3323_);
lean_dec_ref(v___x_3320_);
lean_dec_ref(v_val_3319_);
return v_res_3324_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_3329_ = l_Lean_stringToMessageData(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_3332_ = l_Lean_stringToMessageData(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_3340_ = l_Lean_MessageData_ofFormat(v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
if (lean_obj_tag(v_x_3343_) == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = l_List_reverse___redArg(v_x_3344_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
else
{
lean_object* v_head_3350_; lean_object* v_tail_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3448_; 
v_head_3350_ = lean_ctor_get(v_x_3343_, 0);
v_tail_3351_ = lean_ctor_get(v_x_3343_, 1);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_x_3343_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3353_ = v_x_3343_;
v_isShared_3354_ = v_isSharedCheck_3448_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_tail_3351_);
lean_inc(v_head_3350_);
lean_dec(v_x_3343_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3448_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v_snd_3368_; lean_object* v_fst_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3447_; 
v_snd_3368_ = lean_ctor_get(v_head_3350_, 1);
v_fst_3369_ = lean_ctor_get(v_head_3350_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_head_3350_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3371_ = v_head_3350_;
v_isShared_3372_ = v_isSharedCheck_3447_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snd_3368_);
lean_inc(v_fst_3369_);
lean_dec(v_head_3350_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3447_;
goto v_resetjp_3370_;
}
v___jp_3355_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___y_3356_);
lean_ctor_set(v___x_3360_, 1, v___y_3359_);
v___x_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___y_3358_);
v___x_3362_ = l_Lean_MessageData_nestD(v___x_3361_);
lean_inc_ref(v___y_3357_);
v___x_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___y_3357_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v_x_3344_);
lean_ctor_set(v___x_3353_, 0, v___x_3363_);
v___x_3365_ = v___x_3353_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_x_3344_);
v___x_3365_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
v_x_3343_ = v_tail_3351_;
v_x_3344_ = v___x_3365_;
goto _start;
}
}
v_resetjp_3370_:
{
lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3446_; 
v_fst_3373_ = lean_ctor_get(v_snd_3368_, 0);
v_snd_3374_ = lean_ctor_get(v_snd_3368_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_snd_3368_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3376_ = v_snd_3368_;
v_isShared_3377_ = v_isSharedCheck_3446_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_snd_3374_);
lean_inc(v_fst_3373_);
lean_dec(v_snd_3368_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3446_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v_a_3401_; lean_object* v___y_3417_; lean_object* v___x_3426_; 
v___x_3426_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3342_, v_fst_3369_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_MessageData_nil;
v_a_3401_ = v___x_3427_;
goto v___jp_3400_;
}
else
{
lean_object* v_val_3428_; 
v_val_3428_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_val_3428_);
lean_dec_ref_known(v___x_3426_, 1);
if (lean_obj_tag(v_val_3428_) == 0)
{
lean_object* v_size_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___x_3437_; uint8_t v___x_3438_; 
v_size_3429_ = lean_ctor_get(v_val_3428_, 0);
v___x_3430_ = lean_mk_empty_array_with_capacity(v_size_3429_);
v___x_3431_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_3430_, v_val_3428_);
v___x_3432_ = lean_array_get_size(v___x_3431_);
v___x_3437_ = lean_unsigned_to_nat(0u);
v___x_3438_ = lean_nat_dec_eq(v___x_3432_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___y_3442_; uint8_t v___x_3444_; 
v___x_3439_ = lean_unsigned_to_nat(1u);
v___x_3440_ = lean_nat_sub(v___x_3432_, v___x_3439_);
v___x_3444_ = lean_nat_dec_le(v___x_3437_, v___x_3440_);
if (v___x_3444_ == 0)
{
lean_inc(v___x_3440_);
v___y_3442_ = v___x_3440_;
goto v___jp_3441_;
}
else
{
v___y_3442_ = v___x_3437_;
goto v___jp_3441_;
}
v___jp_3441_:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_nat_dec_le(v___y_3442_, v___x_3440_);
if (v___x_3443_ == 0)
{
lean_dec(v___x_3440_);
lean_inc(v___y_3442_);
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___y_3442_;
goto v___jp_3433_;
}
else
{
v___y_3434_ = v___y_3442_;
v___y_3435_ = v___x_3440_;
goto v___jp_3433_;
}
}
}
else
{
v___y_3417_ = v___x_3431_;
goto v___jp_3416_;
}
v___jp_3433_:
{
lean_object* v___x_3436_; 
v___x_3436_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_3432_, v___x_3431_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
v___y_3417_ = v___x_3436_;
goto v___jp_3416_;
}
}
else
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_MessageData_nil;
v_a_3401_ = v___x_3445_;
goto v___jp_3400_;
}
}
v___jp_3378_:
{
lean_object* v___x_3384_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 7);
lean_ctor_set(v___x_3376_, 1, v___y_3382_);
lean_ctor_set(v___x_3376_, 0, v___y_3380_);
v___x_3384_ = v___x_3376_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___y_3380_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v___y_3382_);
v___x_3384_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
if (lean_obj_tag(v_snd_3374_) == 0)
{
lean_object* v___x_3385_; 
lean_del_object(v___x_3371_);
v___x_3385_ = l_Lean_MessageData_nil;
v___y_3356_ = v___x_3384_;
v___y_3357_ = v___y_3379_;
v___y_3358_ = v___y_3381_;
v___y_3359_ = v___x_3385_;
goto v___jp_3355_;
}
else
{
lean_object* v_val_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v_val_3386_ = lean_ctor_get(v_snd_3374_, 0);
lean_inc_n(v_val_3386_, 2);
lean_dec_ref_known(v_snd_3374_, 1);
v___x_3387_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = lean_string_utf8_byte_size(v_val_3386_);
v___x_3390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3390_, 0, v_val_3386_);
lean_ctor_set(v___x_3390_, 1, v___x_3388_);
lean_ctor_set(v___x_3390_, 2, v___x_3389_);
v___x_3391_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_3392_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_3393_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3386_, v___x_3390_, v___x_3389_, v___x_3391_, v___x_3392_);
lean_dec_ref_known(v___x_3390_, 3);
lean_dec(v_val_3386_);
v___x_3394_ = lean_array_to_list(v___x_3393_);
v___x_3395_ = l_Lean_MessageData_joinSep(v___x_3394_, v___x_3387_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 7);
lean_ctor_set(v___x_3371_, 1, v___x_3395_);
lean_ctor_set(v___x_3371_, 0, v___x_3387_);
v___x_3397_ = v___x_3371_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v___y_3356_ = v___x_3384_;
v___y_3357_ = v___y_3379_;
v___y_3358_ = v___y_3381_;
v___y_3359_ = v___x_3397_;
goto v___jp_3355_;
}
}
}
}
v___jp_3400_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3402_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_3403_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
lean_inc(v_fst_3369_);
v___x_3404_ = l_Lean_MessageData_ofName(v_fst_3369_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___x_3403_);
v___x_3407_ = 1;
v___x_3408_ = l_Lean_Name_toString(v_fst_3369_, v___x_3407_);
v___x_3409_ = lean_string_dec_eq(v___x_3408_, v_fst_3373_);
lean_dec_ref(v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3410_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_3411_ = l_Lean_stringToMessageData(v_fst_3373_);
v___x_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___y_3379_ = v___x_3402_;
v___y_3380_ = v___x_3406_;
v___y_3381_ = v_a_3401_;
v___y_3382_ = v___x_3414_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3415_; 
lean_dec(v_fst_3373_);
v___x_3415_ = l_Lean_MessageData_nil;
v___y_3379_ = v___x_3402_;
v___y_3380_ = v___x_3406_;
v___y_3381_ = v_a_3401_;
v___y_3382_ = v___x_3415_;
goto v___jp_3378_;
}
}
v___jp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_array_to_list(v___y_3417_);
v___x_3419_ = lean_box(0);
v___x_3420_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3341_, v___x_3418_, v___x_3419_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v___x_3422_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3423_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_3424_ = l_Lean_MessageData_joinSep(v_a_3421_, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3422_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v_a_3401_ = v___x_3425_;
goto v___jp_3400_;
}
else
{
lean_del_object(v___x_3376_);
lean_dec(v_snd_3374_);
lean_dec(v_fst_3373_);
lean_del_object(v___x_3371_);
lean_dec(v_fst_3369_);
lean_del_object(v___x_3353_);
lean_dec(v_tail_3351_);
lean_dec(v_x_3344_);
return v___x_3420_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_x_3451_, lean_object* v_x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3449_, v_a_3450_, v_x_3451_, v_x_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v_a_3450_);
lean_dec(v_a_3449_);
return v_res_3456_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_3458_, uint8_t v___y_3459_, lean_object* v_x_3460_){
_start:
{
if (lean_obj_tag(v_x_3460_) == 1)
{
lean_object* v_pre_3461_; 
v_pre_3461_ = lean_ctor_get(v_x_3460_, 0);
if (lean_obj_tag(v_pre_3461_) == 0)
{
lean_object* v_str_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_str_3462_ = lean_ctor_get(v_x_3460_, 1);
v___x_3463_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_3464_ = lean_string_dec_eq(v_str_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
return v___x_3464_;
}
else
{
return v_suppressElabErrors_3458_;
}
}
else
{
return v___y_3459_;
}
}
else
{
return v___y_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_3465_, lean_object* v___y_3466_, lean_object* v_x_3467_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3468_; uint8_t v___y_17928__boxed_3469_; uint8_t v_res_3470_; lean_object* v_r_3471_; 
v_suppressElabErrors_boxed_3468_ = lean_unbox(v_suppressElabErrors_3465_);
v___y_17928__boxed_3469_ = lean_unbox(v___y_3466_);
v_res_3470_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_3468_, v___y_17928__boxed_3469_, v_x_3467_);
lean_dec(v_x_3467_);
v_r_3471_ = lean_box(v_res_3470_);
return v_r_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_3472_, lean_object* v_msgData_3473_, uint8_t v_severity_3474_, uint8_t v_isSilent_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3581_; uint8_t v___y_3582_; uint8_t v___y_3583_; uint8_t v___x_3598_; uint8_t v___y_3600_; uint8_t v___y_3601_; uint8_t v___y_3602_; uint8_t v___y_3604_; uint8_t v___x_3616_; 
v___x_3598_ = 2;
v___x_3616_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3474_, v___x_3598_);
if (v___x_3616_ == 0)
{
v___y_3604_ = v___x_3616_;
goto v___jp_3603_;
}
else
{
uint8_t v___x_3617_; 
lean_inc_ref(v_msgData_3473_);
v___x_3617_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3473_);
v___y_3604_ = v___x_3617_;
goto v___jp_3603_;
}
v___jp_3479_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Elab_Command_getScope___redArg(v___y_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_currNamespace_3490_; lean_object* v___x_3491_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v_currNamespace_3490_ = lean_ctor_get(v_a_3489_, 2);
lean_inc(v_currNamespace_3490_);
lean_dec(v_a_3489_);
v___x_3491_ = l_Lean_Elab_Command_getScope___redArg(v___y_3487_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3527_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3527_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3527_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v_openDecls_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v_env_3501_; lean_object* v_messages_3502_; lean_object* v_scopes_3503_; lean_object* v_usedQuotCtxts_3504_; lean_object* v_nextMacroScope_3505_; lean_object* v_maxRecDepth_3506_; lean_object* v_ngen_3507_; lean_object* v_auxDeclNGen_3508_; lean_object* v_infoState_3509_; lean_object* v_traceState_3510_; lean_object* v_snapshotTasks_3511_; lean_object* v_prevLinterStates_3512_; lean_object* v_codeQualityEntryTasks_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3526_; 
v_openDecls_3496_ = lean_ctor_get(v_a_3492_, 3);
lean_inc(v_openDecls_3496_);
lean_dec(v_a_3492_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v_currNamespace_3490_);
lean_ctor_set(v___x_3497_, 1, v_openDecls_3496_);
v___x_3498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___y_3481_);
lean_inc_ref(v___y_3482_);
lean_inc_ref(v___y_3486_);
v___x_3499_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3499_, 0, v___y_3486_);
lean_ctor_set(v___x_3499_, 1, v___y_3484_);
lean_ctor_set(v___x_3499_, 2, v___y_3485_);
lean_ctor_set(v___x_3499_, 3, v___y_3482_);
lean_ctor_set(v___x_3499_, 4, v___x_3498_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*5, v___y_3480_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*5 + 1, v___y_3483_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*5 + 2, v_isSilent_3475_);
v___x_3500_ = lean_st_ref_take(v___y_3487_);
v_env_3501_ = lean_ctor_get(v___x_3500_, 0);
v_messages_3502_ = lean_ctor_get(v___x_3500_, 1);
v_scopes_3503_ = lean_ctor_get(v___x_3500_, 2);
v_usedQuotCtxts_3504_ = lean_ctor_get(v___x_3500_, 3);
v_nextMacroScope_3505_ = lean_ctor_get(v___x_3500_, 4);
v_maxRecDepth_3506_ = lean_ctor_get(v___x_3500_, 5);
v_ngen_3507_ = lean_ctor_get(v___x_3500_, 6);
v_auxDeclNGen_3508_ = lean_ctor_get(v___x_3500_, 7);
v_infoState_3509_ = lean_ctor_get(v___x_3500_, 8);
v_traceState_3510_ = lean_ctor_get(v___x_3500_, 9);
v_snapshotTasks_3511_ = lean_ctor_get(v___x_3500_, 10);
v_prevLinterStates_3512_ = lean_ctor_get(v___x_3500_, 11);
v_codeQualityEntryTasks_3513_ = lean_ctor_get(v___x_3500_, 12);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3515_ = v___x_3500_;
v_isShared_3516_ = v_isSharedCheck_3526_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3513_);
lean_inc(v_prevLinterStates_3512_);
lean_inc(v_snapshotTasks_3511_);
lean_inc(v_traceState_3510_);
lean_inc(v_infoState_3509_);
lean_inc(v_auxDeclNGen_3508_);
lean_inc(v_ngen_3507_);
lean_inc(v_maxRecDepth_3506_);
lean_inc(v_nextMacroScope_3505_);
lean_inc(v_usedQuotCtxts_3504_);
lean_inc(v_scopes_3503_);
lean_inc(v_messages_3502_);
lean_inc(v_env_3501_);
lean_dec(v___x_3500_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3526_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3517_ = lean_box(0);
v___x_3518_ = l_Lean_MessageLog_add(v___x_3499_, v_messages_3502_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v___x_3518_);
v___x_3520_ = v___x_3515_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_env_3501_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_scopes_3503_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_usedQuotCtxts_3504_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_nextMacroScope_3505_);
lean_ctor_set(v_reuseFailAlloc_3525_, 5, v_maxRecDepth_3506_);
lean_ctor_set(v_reuseFailAlloc_3525_, 6, v_ngen_3507_);
lean_ctor_set(v_reuseFailAlloc_3525_, 7, v_auxDeclNGen_3508_);
lean_ctor_set(v_reuseFailAlloc_3525_, 8, v_infoState_3509_);
lean_ctor_set(v_reuseFailAlloc_3525_, 9, v_traceState_3510_);
lean_ctor_set(v_reuseFailAlloc_3525_, 10, v_snapshotTasks_3511_);
lean_ctor_set(v_reuseFailAlloc_3525_, 11, v_prevLinterStates_3512_);
lean_ctor_set(v_reuseFailAlloc_3525_, 12, v_codeQualityEntryTasks_3513_);
v___x_3520_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_st_ref_put(v___y_3487_, v___x_3520_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3517_);
v___x_3523_ = v___x_3494_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3517_);
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
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_currNamespace_3490_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v___y_3481_);
v_a_3528_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3491_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3491_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v___y_3481_);
v_a_3536_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3488_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3488_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
v___jp_3544_:
{
lean_object* v_fileName_3550_; lean_object* v_fileMap_3551_; uint8_t v_suppressElabErrors_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___f_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3571_; 
v_fileName_3550_ = lean_ctor_get(v___y_3476_, 0);
v_fileMap_3551_ = lean_ctor_get(v___y_3476_, 1);
v_suppressElabErrors_3552_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*10);
v___x_3553_ = lean_box(v_suppressElabErrors_3552_);
v___x_3554_ = lean_box(v___y_3545_);
v___f_3555_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3555_, 0, v___x_3553_);
lean_closure_set(v___f_3555_, 1, v___x_3554_);
v___x_3556_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3473_);
v___x_3557_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v___x_3556_, v___y_3477_);
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3571_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3571_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_inc_ref_n(v_fileMap_3551_, 2);
v___x_3562_ = l_Lean_FileMap_toPosition(v_fileMap_3551_, v___y_3547_);
lean_dec(v___y_3547_);
v___x_3563_ = l_Lean_FileMap_toPosition(v_fileMap_3551_, v___y_3549_);
lean_dec(v___y_3549_);
v___x_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
v___x_3565_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_suppressElabErrors_3552_ == 0)
{
lean_del_object(v___x_3560_);
lean_dec_ref(v___f_3555_);
v___y_3480_ = v___y_3546_;
v___y_3481_ = v_a_3558_;
v___y_3482_ = v___x_3565_;
v___y_3483_ = v___y_3548_;
v___y_3484_ = v___x_3562_;
v___y_3485_ = v___x_3564_;
v___y_3486_ = v_fileName_3550_;
v___y_3487_ = v___y_3477_;
goto v___jp_3479_;
}
else
{
uint8_t v___x_3566_; 
lean_inc(v_a_3558_);
v___x_3566_ = l_Lean_MessageData_hasTag(v___f_3555_, v_a_3558_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3569_; 
lean_dec_ref_known(v___x_3564_, 1);
lean_dec_ref(v___x_3562_);
lean_dec(v_a_3558_);
v___x_3567_ = lean_box(0);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3567_);
v___x_3569_ = v___x_3560_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
else
{
lean_del_object(v___x_3560_);
v___y_3480_ = v___y_3546_;
v___y_3481_ = v_a_3558_;
v___y_3482_ = v___x_3565_;
v___y_3483_ = v___y_3548_;
v___y_3484_ = v___x_3562_;
v___y_3485_ = v___x_3564_;
v___y_3486_ = v_fileName_3550_;
v___y_3487_ = v___y_3477_;
goto v___jp_3479_;
}
}
}
}
v___jp_3572_:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Syntax_getTailPos_x3f(v___y_3574_, v___y_3575_);
lean_dec(v___y_3574_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_inc(v___y_3577_);
v___y_3545_ = v___y_3573_;
v___y_3546_ = v___y_3575_;
v___y_3547_ = v___y_3577_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v___y_3577_;
goto v___jp_3544_;
}
else
{
lean_object* v_val_3579_; 
v_val_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_val_3579_);
lean_dec_ref_known(v___x_3578_, 1);
v___y_3545_ = v___y_3573_;
v___y_3546_ = v___y_3575_;
v___y_3547_ = v___y_3577_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v_val_3579_;
goto v___jp_3544_;
}
}
v___jp_3580_:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_Elab_Command_getRef___redArg(v___y_3476_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v_ref_3586_; lean_object* v___x_3587_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3584_, 1);
v_ref_3586_ = l_Lean_replaceRef(v_ref_3472_, v_a_3585_);
lean_dec(v_a_3585_);
v___x_3587_ = l_Lean_Syntax_getPos_x3f(v_ref_3586_, v___y_3582_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_unsigned_to_nat(0u);
v___y_3573_ = v___y_3581_;
v___y_3574_ = v_ref_3586_;
v___y_3575_ = v___y_3582_;
v___y_3576_ = v___y_3583_;
v___y_3577_ = v___x_3588_;
goto v___jp_3572_;
}
else
{
lean_object* v_val_3589_; 
v_val_3589_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_val_3589_);
lean_dec_ref_known(v___x_3587_, 1);
v___y_3573_ = v___y_3581_;
v___y_3574_ = v_ref_3586_;
v___y_3575_ = v___y_3582_;
v___y_3576_ = v___y_3583_;
v___y_3577_ = v_val_3589_;
goto v___jp_3572_;
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_msgData_3473_);
v_a_3590_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3584_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3584_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
v___jp_3599_:
{
if (v___y_3602_ == 0)
{
v___y_3581_ = v___y_3600_;
v___y_3582_ = v___y_3601_;
v___y_3583_ = v_severity_3474_;
goto v___jp_3580_;
}
else
{
v___y_3581_ = v___y_3600_;
v___y_3582_ = v___y_3601_;
v___y_3583_ = v___x_3598_;
goto v___jp_3580_;
}
}
v___jp_3603_:
{
if (v___y_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_scopes_3607_; lean_object* v___x_3608_; lean_object* v_opts_3609_; uint8_t v___x_3610_; uint8_t v___x_3611_; 
v___x_3605_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3606_ = lean_st_ref_get(v___y_3477_);
v_scopes_3607_ = lean_ctor_get(v___x_3606_, 2);
lean_inc(v_scopes_3607_);
lean_dec(v___x_3606_);
v___x_3608_ = l_List_head_x21___redArg(v___x_3605_, v_scopes_3607_);
lean_dec(v_scopes_3607_);
v_opts_3609_ = lean_ctor_get(v___x_3608_, 1);
lean_inc_ref(v_opts_3609_);
lean_dec(v___x_3608_);
v___x_3610_ = 1;
v___x_3611_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3474_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_dec_ref(v_opts_3609_);
v___y_3600_ = v___y_3604_;
v___y_3601_ = v___y_3604_;
v___y_3602_ = v___x_3611_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3612_ = l_Lean_warningAsError;
v___x_3613_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_3609_, v___x_3612_);
lean_dec_ref(v_opts_3609_);
v___y_3600_ = v___y_3604_;
v___y_3601_ = v___y_3604_;
v___y_3602_ = v___x_3613_;
goto v___jp_3599_;
}
}
else
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v_msgData_3473_);
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_3618_, lean_object* v_msgData_3619_, lean_object* v_severity_3620_, lean_object* v_isSilent_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v_severity_boxed_3625_; uint8_t v_isSilent_boxed_3626_; lean_object* v_res_3627_; 
v_severity_boxed_3625_ = lean_unbox(v_severity_3620_);
v_isSilent_boxed_3626_ = lean_unbox(v_isSilent_3621_);
v_res_3627_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3618_, v_msgData_3619_, v_severity_boxed_3625_, v_isSilent_boxed_3626_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v_ref_3618_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_3628_, uint8_t v_severity_3629_, uint8_t v_isSilent_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_Elab_Command_getRef___redArg(v___y_3631_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3636_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
v___x_3636_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_3635_, v_msgData_3628_, v_severity_3629_, v_isSilent_3630_, v___y_3631_, v___y_3632_);
lean_dec(v_a_3635_);
return v___x_3636_;
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec_ref(v_msgData_3628_);
v_a_3637_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3634_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3634_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_3645_, lean_object* v_severity_3646_, lean_object* v_isSilent_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v_severity_boxed_3651_; uint8_t v_isSilent_boxed_3652_; lean_object* v_res_3653_; 
v_severity_boxed_3651_ = lean_unbox(v_severity_3646_);
v_isSilent_boxed_3652_ = lean_unbox(v_isSilent_3647_);
v_res_3653_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3645_, v_severity_boxed_3651_, v_isSilent_boxed_3652_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
uint8_t v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = 0;
v___x_3659_ = 0;
v___x_3660_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3654_, v___x_3658_, v___x_3659_, v___y_3655_, v___y_3656_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_3666_, lean_object* v_x_3667_){
_start:
{
if (lean_obj_tag(v_x_3667_) == 0)
{
lean_object* v_k_3669_; lean_object* v_v_3670_; lean_object* v_l_3671_; lean_object* v_r_3672_; lean_object* v___x_3673_; lean_object* v_a_3674_; lean_object* v_a_3675_; lean_object* v___x_3676_; 
v_k_3669_ = lean_ctor_get(v_x_3667_, 1);
lean_inc(v_k_3669_);
v_v_3670_ = lean_ctor_get(v_x_3667_, 2);
lean_inc(v_v_3670_);
v_l_3671_ = lean_ctor_get(v_x_3667_, 3);
lean_inc(v_l_3671_);
v_r_3672_ = lean_ctor_get(v_x_3667_, 4);
lean_inc(v_r_3672_);
lean_dec_ref_known(v_x_3667_, 5);
v___x_3673_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3666_, v_l_3671_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v_a_3675_ = lean_ctor_get(v_a_3674_, 0);
lean_inc(v_a_3675_);
lean_dec(v_a_3674_);
v___x_3676_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3669_, v_v_3670_, v_a_3675_);
v_init_3666_ = v___x_3676_;
v_x_3667_ = v_r_3672_;
goto _start;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3678_, 0, v_init_3666_);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_3680_, lean_object* v_x_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3680_, v_x_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_3684_, lean_object* v_x1_3685_, lean_object* v_x2_3686_){
_start:
{
lean_object* v_fst_3687_; lean_object* v_fst_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v_fst_3687_ = lean_ctor_get(v_x1_3685_, 0);
lean_inc(v_fst_3687_);
lean_dec_ref(v_x1_3685_);
v_fst_3688_ = lean_ctor_get(v_x2_3686_, 0);
lean_inc(v_fst_3688_);
lean_dec_ref(v_x2_3686_);
v___x_3689_ = l_Lean_Name_toString(v_fst_3687_, v___x_3684_);
v___x_3690_ = l_Lean_Name_toString(v_fst_3688_, v___x_3684_);
v___x_3691_ = lean_string_dec_lt(v___x_3689_, v___x_3690_);
lean_dec_ref(v___x_3690_);
lean_dec_ref(v___x_3689_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_3692_, lean_object* v_x1_3693_, lean_object* v_x2_3694_){
_start:
{
uint8_t v___x_18271__boxed_3695_; uint8_t v_res_3696_; lean_object* v_r_3697_; 
v___x_18271__boxed_3695_ = lean_unbox(v___x_3692_);
v_res_3696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18271__boxed_3695_, v_x1_3693_, v_x2_3694_);
v_r_3697_ = lean_box(v_res_3696_);
return v_r_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_3698_, lean_object* v_pivot_3699_, lean_object* v_as_3700_, lean_object* v_i_3701_, lean_object* v_k_3702_){
_start:
{
uint8_t v___x_3703_; 
v___x_3703_ = lean_nat_dec_lt(v_k_3702_, v_hi_3698_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_dec(v_k_3702_);
lean_dec_ref(v_pivot_3699_);
v___x_3704_ = lean_array_fswap(v_as_3700_, v_i_3701_, v_hi_3698_);
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v_i_3701_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
return v___x_3705_;
}
else
{
lean_object* v___x_3706_; lean_object* v_fst_3707_; lean_object* v_fst_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3706_ = lean_array_fget_borrowed(v_as_3700_, v_k_3702_);
v_fst_3707_ = lean_ctor_get(v___x_3706_, 0);
v_fst_3708_ = lean_ctor_get(v_pivot_3699_, 0);
lean_inc(v_fst_3707_);
v___x_3709_ = l_Lean_Name_toString(v_fst_3707_, v___x_3703_);
lean_inc(v_fst_3708_);
v___x_3710_ = l_Lean_Name_toString(v_fst_3708_, v___x_3703_);
v___x_3711_ = lean_string_dec_lt(v___x_3709_, v___x_3710_);
lean_dec_ref(v___x_3710_);
lean_dec_ref(v___x_3709_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_unsigned_to_nat(1u);
v___x_3713_ = lean_nat_add(v_k_3702_, v___x_3712_);
lean_dec(v_k_3702_);
v_k_3702_ = v___x_3713_;
goto _start;
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3715_ = lean_array_fswap(v_as_3700_, v_i_3701_, v_k_3702_);
v___x_3716_ = lean_unsigned_to_nat(1u);
v___x_3717_ = lean_nat_add(v_i_3701_, v___x_3716_);
lean_dec(v_i_3701_);
v___x_3718_ = lean_nat_add(v_k_3702_, v___x_3716_);
lean_dec(v_k_3702_);
v_as_3700_ = v___x_3715_;
v_i_3701_ = v___x_3717_;
v_k_3702_ = v___x_3718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_3720_, lean_object* v_pivot_3721_, lean_object* v_as_3722_, lean_object* v_i_3723_, lean_object* v_k_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3720_, v_pivot_3721_, v_as_3722_, v_i_3723_, v_k_3724_);
lean_dec(v_hi_3720_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_3726_, lean_object* v_as_3727_, lean_object* v_lo_3728_, lean_object* v_hi_3729_){
_start:
{
lean_object* v___y_3731_; uint8_t v___x_3741_; 
v___x_3741_ = lean_nat_dec_lt(v_lo_3728_, v_hi_3729_);
if (v___x_3741_ == 0)
{
lean_dec(v_lo_3728_);
return v_as_3727_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v_mid_3744_; lean_object* v___y_3746_; lean_object* v___y_3752_; lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3742_ = lean_nat_add(v_lo_3728_, v_hi_3729_);
v___x_3743_ = lean_unsigned_to_nat(1u);
v_mid_3744_ = lean_nat_shiftr(v___x_3742_, v___x_3743_);
lean_dec(v___x_3742_);
v___x_3757_ = lean_array_fget_borrowed(v_as_3727_, v_mid_3744_);
v___x_3758_ = lean_array_fget_borrowed(v_as_3727_, v_lo_3728_);
lean_inc(v___x_3758_);
lean_inc(v___x_3757_);
v___x_3759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3741_, v___x_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
v___y_3752_ = v_as_3727_;
goto v___jp_3751_;
}
else
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_array_fswap(v_as_3727_, v_lo_3728_, v_mid_3744_);
v___y_3752_ = v___x_3760_;
goto v___jp_3751_;
}
v___jp_3745_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3747_ = lean_array_fget_borrowed(v___y_3746_, v_mid_3744_);
v___x_3748_ = lean_array_fget_borrowed(v___y_3746_, v_hi_3729_);
lean_inc(v___x_3748_);
lean_inc(v___x_3747_);
v___x_3749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3741_, v___x_3747_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_dec(v_mid_3744_);
v___y_3731_ = v___y_3746_;
goto v___jp_3730_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_array_fswap(v___y_3746_, v_mid_3744_, v_hi_3729_);
lean_dec(v_mid_3744_);
v___y_3731_ = v___x_3750_;
goto v___jp_3730_;
}
}
v___jp_3751_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3753_ = lean_array_fget_borrowed(v___y_3752_, v_hi_3729_);
v___x_3754_ = lean_array_fget_borrowed(v___y_3752_, v_lo_3728_);
lean_inc(v___x_3754_);
lean_inc(v___x_3753_);
v___x_3755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3741_, v___x_3753_, v___x_3754_);
if (v___x_3755_ == 0)
{
v___y_3746_ = v___y_3752_;
goto v___jp_3745_;
}
else
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_array_fswap(v___y_3752_, v_lo_3728_, v_hi_3729_);
v___y_3746_ = v___x_3756_;
goto v___jp_3745_;
}
}
}
v___jp_3730_:
{
lean_object* v_pivot_3732_; lean_object* v___x_3733_; lean_object* v_fst_3734_; lean_object* v_snd_3735_; uint8_t v___x_3736_; 
v_pivot_3732_ = lean_array_fget(v___y_3731_, v_hi_3729_);
lean_inc_n(v_lo_3728_, 2);
v___x_3733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3729_, v_pivot_3732_, v___y_3731_, v_lo_3728_, v_lo_3728_);
v_fst_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_fst_3734_);
v_snd_3735_ = lean_ctor_get(v___x_3733_, 1);
lean_inc(v_snd_3735_);
lean_dec_ref(v___x_3733_);
v___x_3736_ = lean_nat_dec_le(v_hi_3729_, v_fst_3734_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3726_, v_snd_3735_, v_lo_3728_, v_fst_3734_);
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = lean_nat_add(v_fst_3734_, v___x_3738_);
lean_dec(v_fst_3734_);
v_as_3727_ = v___x_3737_;
v_lo_3728_ = v___x_3739_;
goto _start;
}
else
{
lean_dec(v_fst_3734_);
lean_dec(v_lo_3728_);
return v_snd_3735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_3761_, lean_object* v_as_3762_, lean_object* v_lo_3763_, lean_object* v_hi_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3761_, v_as_3762_, v_lo_3763_, v_hi_3764_);
lean_dec(v_hi_3764_);
lean_dec(v_n_3761_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_3766_, lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 0)
{
lean_object* v_k_3768_; lean_object* v_v_3769_; lean_object* v_l_3770_; lean_object* v_r_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v_k_3768_ = lean_ctor_get(v_x_3767_, 1);
v_v_3769_ = lean_ctor_get(v_x_3767_, 2);
v_l_3770_ = lean_ctor_get(v_x_3767_, 3);
v_r_3771_ = lean_ctor_get(v_x_3767_, 4);
v___x_3772_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3766_, v_l_3770_);
lean_inc(v_v_3769_);
lean_inc(v_k_3768_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v_k_3768_);
lean_ctor_set(v___x_3773_, 1, v_v_3769_);
v___x_3774_ = lean_array_push(v___x_3772_, v___x_3773_);
v_init_3766_ = v___x_3774_;
v_x_3767_ = v_r_3771_;
goto _start;
}
else
{
return v_init_3766_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_3776_, lean_object* v_x_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3776_, v_x_3777_);
lean_dec(v_x_3777_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_3779_, size_t v_sz_3780_, size_t v_i_3781_, lean_object* v_b_3782_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3781_, v_sz_3780_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_b_3782_);
return v___x_3785_;
}
else
{
lean_object* v_a_3786_; lean_object* v_fst_3787_; lean_object* v_snd_3788_; lean_object* v_found_3789_; size_t v___x_3790_; size_t v___x_3791_; 
v_a_3786_ = lean_array_uget_borrowed(v_as_3779_, v_i_3781_);
v_fst_3787_ = lean_ctor_get(v_a_3786_, 0);
v_snd_3788_ = lean_ctor_get(v_a_3786_, 1);
lean_inc(v_snd_3788_);
lean_inc(v_fst_3787_);
v_found_3789_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3787_, v_snd_3788_, v_b_3782_);
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3781_, v___x_3790_);
v_i_3781_ = v___x_3791_;
v_b_3782_ = v_found_3789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_3793_, lean_object* v_sz_3794_, lean_object* v_i_3795_, lean_object* v_b_3796_, lean_object* v___y_3797_){
_start:
{
size_t v_sz_boxed_3798_; size_t v_i_boxed_3799_; lean_object* v_res_3800_; 
v_sz_boxed_3798_ = lean_unbox_usize(v_sz_3794_);
lean_dec(v_sz_3794_);
v_i_boxed_3799_ = lean_unbox_usize(v_i_3795_);
lean_dec(v_i_3795_);
v_res_3800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3793_, v_sz_boxed_3798_, v_i_boxed_3799_, v_b_3796_);
lean_dec_ref(v_as_3793_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3801_, size_t v_sz_3802_, size_t v_i_3803_, lean_object* v_b_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
uint8_t v___x_3808_; 
v___x_3808_ = lean_usize_dec_lt(v_i_3803_, v_sz_3802_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v_b_3804_);
return v___x_3809_;
}
else
{
lean_object* v_a_3810_; size_t v_sz_3811_; size_t v___x_3812_; lean_object* v___x_3813_; 
v_a_3810_ = lean_array_uget_borrowed(v_as_3801_, v_i_3803_);
v_sz_3811_ = lean_array_size(v_a_3810_);
v___x_3812_ = ((size_t)0ULL);
v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_3810_, v_sz_3811_, v___x_3812_, v_b_3804_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; size_t v___x_3815_; size_t v___x_3816_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v___x_3815_ = ((size_t)1ULL);
v___x_3816_ = lean_usize_add(v_i_3803_, v___x_3815_);
v_i_3803_ = v___x_3816_;
v_b_3804_ = v_a_3814_;
goto _start;
}
else
{
return v___x_3813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3818_, lean_object* v_sz_3819_, lean_object* v_i_3820_, lean_object* v_b_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
size_t v_sz_boxed_3825_; size_t v_i_boxed_3826_; lean_object* v_res_3827_; 
v_sz_boxed_3825_ = lean_unbox_usize(v_sz_3819_);
lean_dec(v_sz_3819_);
v_i_boxed_3826_ = lean_unbox_usize(v_i_3820_);
lean_dec(v_i_3820_);
v_res_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3818_, v_sz_boxed_3825_, v_i_boxed_3826_, v_b_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v_as_3818_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___y_3834_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v_env_3852_; lean_object* v___x_3853_; lean_object* v_toEnvExtension_3854_; lean_object* v_asyncMode_3855_; lean_object* v___x_3856_; lean_object* v_a_3858_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v_a_3884_; 
v___x_3849_ = lean_box(1);
v___x_3850_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3851_ = lean_st_ref_get(v___y_3831_);
v_env_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc_ref_n(v_env_3852_, 2);
lean_dec(v___x_3851_);
v___x_3853_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_3854_ = lean_ctor_get(v___x_3853_, 0);
v_asyncMode_3855_ = lean_ctor_get(v_toEnvExtension_3854_, 2);
v___x_3856_ = lean_box(0);
v___x_3881_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3849_, v___x_3853_, v_env_3852_, v_asyncMode_3855_, v___x_3856_);
v___x_3882_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_3849_, v___x_3881_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v_a_3884_ = lean_ctor_get(v_a_3883_, 0);
lean_inc(v_a_3884_);
lean_dec(v_a_3883_);
v_a_3858_ = v_a_3884_;
goto v___jp_3857_;
v___jp_3833_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = lean_array_to_list(v___y_3834_);
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
return v___x_3836_;
}
v___jp_3837_:
{
lean_object* v___x_3842_; 
v___x_3842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_3840_, v___y_3839_, v___y_3838_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
v___y_3834_ = v___x_3842_;
goto v___jp_3833_;
}
v___jp_3843_:
{
uint8_t v___x_3848_; 
v___x_3848_ = lean_nat_dec_le(v___y_3847_, v___y_3844_);
if (v___x_3848_ == 0)
{
lean_dec(v___y_3844_);
lean_inc(v___y_3847_);
v___y_3838_ = v___y_3847_;
v___y_3839_ = v___y_3845_;
v___y_3840_ = v___y_3846_;
v___y_3841_ = v___y_3847_;
goto v___jp_3837_;
}
else
{
v___y_3838_ = v___y_3847_;
v___y_3839_ = v___y_3845_;
v___y_3840_ = v___y_3846_;
v___y_3841_ = v___y_3844_;
goto v___jp_3837_;
}
}
v___jp_3857_:
{
lean_object* v___x_3859_; lean_object* v_importedEntries_3860_; size_t v_sz_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v___x_3859_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3850_, v_toEnvExtension_3854_, v_env_3852_, v_asyncMode_3855_, v___x_3856_);
v_importedEntries_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc_ref(v_importedEntries_3860_);
lean_dec(v___x_3859_);
v_sz_3861_ = lean_array_size(v_importedEntries_3860_);
v___x_3862_ = ((size_t)0ULL);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_3860_, v_sz_3861_, v___x_3862_, v_a_3858_, v___y_3830_, v___y_3831_);
lean_dec_ref(v_importedEntries_3860_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_arr_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_3867_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_3866_, v_a_3864_);
lean_dec(v_a_3864_);
v___x_3868_ = lean_array_get_size(v_arr_3867_);
v___x_3869_ = lean_nat_dec_eq(v___x_3868_, v___x_3865_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3870_ = lean_unsigned_to_nat(1u);
v___x_3871_ = lean_nat_sub(v___x_3868_, v___x_3870_);
v___x_3872_ = lean_nat_dec_le(v___x_3865_, v___x_3871_);
if (v___x_3872_ == 0)
{
lean_inc(v___x_3871_);
v___y_3844_ = v___x_3871_;
v___y_3845_ = v_arr_3867_;
v___y_3846_ = v___x_3868_;
v___y_3847_ = v___x_3871_;
goto v___jp_3843_;
}
else
{
v___y_3844_ = v___x_3871_;
v___y_3845_ = v_arr_3867_;
v___y_3846_ = v___x_3868_;
v___y_3847_ = v___x_3865_;
goto v___jp_3843_;
}
}
else
{
v___y_3834_ = v_arr_3867_;
goto v___jp_3833_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
v_a_3873_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3863_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3863_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_3889_, lean_object* v_k_3890_, lean_object* v_fallback_3891_){
_start:
{
if (lean_obj_tag(v_t_3889_) == 0)
{
lean_object* v_k_3892_; lean_object* v_v_3893_; lean_object* v_l_3894_; lean_object* v_r_3895_; uint8_t v___x_3896_; 
v_k_3892_ = lean_ctor_get(v_t_3889_, 1);
v_v_3893_ = lean_ctor_get(v_t_3889_, 2);
v_l_3894_ = lean_ctor_get(v_t_3889_, 3);
v_r_3895_ = lean_ctor_get(v_t_3889_, 4);
v___x_3896_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3890_, v_k_3892_);
switch(v___x_3896_)
{
case 0:
{
v_t_3889_ = v_l_3894_;
goto _start;
}
case 1:
{
lean_inc(v_v_3893_);
return v_v_3893_;
}
default: 
{
v_t_3889_ = v_r_3895_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3891_);
return v_fallback_3891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_3899_, lean_object* v_k_3900_, lean_object* v_fallback_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3899_, v_k_3900_, v_fallback_3901_);
lean_dec(v_fallback_3901_);
lean_dec(v_k_3900_);
lean_dec(v_t_3899_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_3903_, size_t v_sz_3904_, size_t v_i_3905_, lean_object* v_b_3906_){
_start:
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_usize_dec_lt(v_i_3905_, v_sz_3904_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; 
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v_b_3906_);
return v___x_3909_;
}
else
{
lean_object* v_a_3910_; lean_object* v_fst_3911_; lean_object* v_snd_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; size_t v___x_3917_; size_t v___x_3918_; 
v_a_3910_ = lean_array_uget_borrowed(v_as_3903_, v_i_3905_);
v_fst_3911_ = lean_ctor_get(v_a_3910_, 0);
v_snd_3912_ = lean_ctor_get(v_a_3910_, 1);
v___x_3913_ = l_Lean_NameSet_empty;
v___x_3914_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3906_, v_snd_3912_, v___x_3913_);
lean_inc(v_fst_3911_);
v___x_3915_ = l_Lean_NameSet_insert(v___x_3914_, v_fst_3911_);
lean_inc(v_snd_3912_);
v___x_3916_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_3912_, v___x_3915_, v_b_3906_);
v___x_3917_ = ((size_t)1ULL);
v___x_3918_ = lean_usize_add(v_i_3905_, v___x_3917_);
v_i_3905_ = v___x_3918_;
v_b_3906_ = v___x_3916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_3920_, lean_object* v_sz_3921_, lean_object* v_i_3922_, lean_object* v_b_3923_, lean_object* v___y_3924_){
_start:
{
size_t v_sz_boxed_3925_; size_t v_i_boxed_3926_; lean_object* v_res_3927_; 
v_sz_boxed_3925_ = lean_unbox_usize(v_sz_3921_);
lean_dec(v_sz_3921_);
v_i_boxed_3926_ = lean_unbox_usize(v_i_3922_);
lean_dec(v_i_3922_);
v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3920_, v_sz_boxed_3925_, v_i_boxed_3926_, v_b_3923_);
lean_dec_ref(v_as_3920_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_3928_, size_t v_sz_3929_, size_t v_i_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
uint8_t v___x_3935_; 
v___x_3935_ = lean_usize_dec_lt(v_i_3930_, v_sz_3929_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3936_, 0, v_b_3931_);
return v___x_3936_;
}
else
{
lean_object* v_a_3937_; size_t v_sz_3938_; size_t v___x_3939_; lean_object* v___x_3940_; 
v_a_3937_ = lean_array_uget_borrowed(v_as_3928_, v_i_3930_);
v_sz_3938_ = lean_array_size(v_a_3937_);
v___x_3939_ = ((size_t)0ULL);
v___x_3940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_3937_, v_sz_3938_, v___x_3939_, v_b_3931_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; size_t v___x_3942_; size_t v___x_3943_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_add(v_i_3930_, v___x_3942_);
v_i_3930_ = v___x_3943_;
v_b_3931_ = v_a_3941_;
goto _start;
}
else
{
return v___x_3940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_3945_, lean_object* v_sz_3946_, lean_object* v_i_3947_, lean_object* v_b_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
size_t v_sz_boxed_3952_; size_t v_i_boxed_3953_; lean_object* v_res_3954_; 
v_sz_boxed_3952_ = lean_unbox_usize(v_sz_3946_);
lean_dec(v_sz_3946_);
v_i_boxed_3953_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_3945_, v_sz_boxed_3952_, v_i_boxed_3953_, v_b_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec_ref(v_as_3945_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_3955_, size_t v_i_3956_, size_t v_stop_3957_, lean_object* v_b_3958_){
_start:
{
uint8_t v___x_3959_; 
v___x_3959_ = lean_usize_dec_eq(v_i_3956_, v_stop_3957_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v_fst_3961_; lean_object* v_snd_3962_; lean_object* v___x_3963_; size_t v___x_3964_; size_t v___x_3965_; 
v___x_3960_ = lean_array_uget_borrowed(v_as_3955_, v_i_3956_);
v_fst_3961_ = lean_ctor_get(v___x_3960_, 0);
v_snd_3962_ = lean_ctor_get(v___x_3960_, 1);
lean_inc(v_snd_3962_);
lean_inc(v_fst_3961_);
v___x_3963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3961_, v_snd_3962_, v_b_3958_);
v___x_3964_ = ((size_t)1ULL);
v___x_3965_ = lean_usize_add(v_i_3956_, v___x_3964_);
v_i_3956_ = v___x_3965_;
v_b_3958_ = v___x_3963_;
goto _start;
}
else
{
return v_b_3958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_3967_, lean_object* v_i_3968_, lean_object* v_stop_3969_, lean_object* v_b_3970_){
_start:
{
size_t v_i_boxed_3971_; size_t v_stop_boxed_3972_; lean_object* v_res_3973_; 
v_i_boxed_3971_ = lean_unbox_usize(v_i_3968_);
lean_dec(v_i_3968_);
v_stop_boxed_3972_ = lean_unbox_usize(v_stop_3969_);
lean_dec(v_stop_3969_);
v_res_3973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_3967_, v_i_boxed_3971_, v_stop_boxed_3972_, v_b_3970_);
lean_dec_ref(v_as_3967_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_3974_, size_t v_i_3975_, size_t v_stop_3976_, lean_object* v_b_3977_){
_start:
{
lean_object* v___y_3979_; uint8_t v___x_3983_; 
v___x_3983_ = lean_usize_dec_eq(v_i_3975_, v_stop_3976_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v___x_3984_ = lean_array_uget_borrowed(v_as_3974_, v_i_3975_);
v___x_3985_ = lean_unsigned_to_nat(0u);
v___x_3986_ = lean_array_get_size(v___x_3984_);
v___x_3987_ = lean_nat_dec_lt(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
v___y_3979_ = v_b_3977_;
goto v___jp_3978_;
}
else
{
size_t v___x_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
v___x_3988_ = ((size_t)0ULL);
v___x_3989_ = lean_usize_of_nat(v___x_3986_);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_3984_, v___x_3988_, v___x_3989_, v_b_3977_);
v___y_3979_ = v___x_3990_;
goto v___jp_3978_;
}
}
else
{
return v_b_3977_;
}
v___jp_3978_:
{
size_t v___x_3980_; size_t v___x_3981_; 
v___x_3980_ = ((size_t)1ULL);
v___x_3981_ = lean_usize_add(v_i_3975_, v___x_3980_);
v_i_3975_ = v___x_3981_;
v_b_3977_ = v___y_3979_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_3991_, lean_object* v_i_3992_, lean_object* v_stop_3993_, lean_object* v_b_3994_){
_start:
{
size_t v_i_boxed_3995_; size_t v_stop_boxed_3996_; lean_object* v_res_3997_; 
v_i_boxed_3995_ = lean_unbox_usize(v_i_3992_);
lean_dec(v_i_3992_);
v_stop_boxed_3996_ = lean_unbox_usize(v_stop_3993_);
lean_dec(v_stop_3993_);
v_res_3997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_3991_, v_i_boxed_3995_, v_stop_boxed_3996_, v_b_3994_);
lean_dec_ref(v_as_3991_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_3998_){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v_env_4004_; lean_object* v___x_4005_; lean_object* v_ext_4006_; lean_object* v_toEnvExtension_4007_; lean_object* v_asyncMode_4008_; lean_object* v___x_4009_; lean_object* v_categories_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4000_ = lean_box(1);
v___x_4001_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4002_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4003_ = lean_st_ref_get(v___y_3998_);
v_env_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc_ref_n(v_env_4004_, 2);
lean_dec(v___x_4003_);
v___x_4005_ = l_Lean_Parser_parserExtension;
v_ext_4006_ = lean_ctor_get(v___x_4005_, 1);
v_toEnvExtension_4007_ = lean_ctor_get(v_ext_4006_, 0);
v_asyncMode_4008_ = lean_ctor_get(v_toEnvExtension_4007_, 2);
v___x_4009_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4002_, v___x_4005_, v_env_4004_, v_asyncMode_4008_);
v_categories_4010_ = lean_ctor_get(v___x_4009_, 2);
lean_inc_ref(v_categories_4010_);
lean_dec(v___x_4009_);
v___x_4011_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4012_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4010_, v___x_4011_);
lean_dec_ref(v_categories_4010_);
if (lean_obj_tag(v___x_4012_) == 1)
{
lean_object* v_val_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4044_; 
v_val_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4044_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_val_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4044_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___y_4018_; lean_object* v___x_4027_; lean_object* v_toEnvExtension_4028_; lean_object* v_exportEntriesFn_4029_; lean_object* v_asyncMode_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v_importedEntries_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v_exported_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4027_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4028_ = lean_ctor_get(v___x_4027_, 0);
v_exportEntriesFn_4029_ = lean_ctor_get(v___x_4027_, 4);
v_asyncMode_4030_ = lean_ctor_get(v_toEnvExtension_4028_, 2);
v___x_4031_ = lean_box(0);
lean_inc_ref_n(v_env_4004_, 2);
v___x_4032_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4001_, v_toEnvExtension_4028_, v_env_4004_, v_asyncMode_4030_, v___x_4031_);
v_importedEntries_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc_ref(v_importedEntries_4033_);
lean_dec(v___x_4032_);
v___x_4034_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4000_, v___x_4027_, v_env_4004_, v_asyncMode_4030_, v___x_4031_);
lean_inc_ref(v_exportEntriesFn_4029_);
v___x_4035_ = lean_apply_2(v_exportEntriesFn_4029_, v_env_4004_, v___x_4034_);
v_exported_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_exported_4036_);
lean_dec_ref(v___x_4035_);
v___x_4037_ = lean_array_push(v_importedEntries_4033_, v_exported_4036_);
v___x_4038_ = lean_unsigned_to_nat(0u);
v___x_4039_ = lean_array_get_size(v___x_4037_);
v___x_4040_ = lean_nat_dec_lt(v___x_4038_, v___x_4039_);
if (v___x_4040_ == 0)
{
lean_dec_ref(v___x_4037_);
v___y_4018_ = v___x_4000_;
goto v___jp_4017_;
}
else
{
size_t v___x_4041_; size_t v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = ((size_t)0ULL);
v___x_4042_ = lean_usize_of_nat(v___x_4039_);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4037_, v___x_4041_, v___x_4042_, v___x_4000_);
lean_dec_ref(v___x_4037_);
v___y_4018_ = v___x_4043_;
goto v___jp_4017_;
}
v___jp_4017_:
{
lean_object* v_tables_4019_; lean_object* v_leadingTable_4020_; lean_object* v_trailingTable_4021_; lean_object* v_firstTokens_4022_; lean_object* v_firstTokens_4023_; lean_object* v___x_4025_; 
v_tables_4019_ = lean_ctor_get(v_val_4013_, 2);
v_leadingTable_4020_ = lean_ctor_get(v_tables_4019_, 0);
v_trailingTable_4021_ = lean_ctor_get(v_tables_4019_, 2);
lean_inc(v_trailingTable_4021_);
lean_inc(v_leadingTable_4020_);
lean_inc(v_val_4013_);
v_firstTokens_4022_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4013_, v_leadingTable_4020_, v___y_4018_);
v_firstTokens_4023_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4013_, v_trailingTable_4021_, v_firstTokens_4022_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set_tag(v___x_4015_, 0);
lean_ctor_set(v___x_4015_, 0, v_firstTokens_4023_);
v___x_4025_ = v___x_4015_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_firstTokens_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_object* v___x_4045_; 
lean_dec(v___x_4012_);
lean_dec_ref(v_env_4004_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4000_);
return v___x_4045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4046_);
lean_dec(v___y_4046_);
return v_res_4048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_4051_ = l_Lean_stringToMessageData(v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v_env_4058_; lean_object* v___x_4059_; lean_object* v_env_4060_; lean_object* v___x_4061_; lean_object* v_env_4062_; lean_object* v___x_4063_; lean_object* v_toEnvExtension_4064_; lean_object* v_exportEntriesFn_4065_; lean_object* v_asyncMode_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v_importedEntries_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4121_; 
v___x_4055_ = lean_box(1);
v___x_4056_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4057_ = lean_st_ref_get(v_a_4053_);
v_env_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc_ref(v_env_4058_);
lean_dec(v___x_4057_);
v___x_4059_ = lean_st_ref_get(v_a_4053_);
v_env_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc_ref(v_env_4060_);
lean_dec(v___x_4059_);
v___x_4061_ = lean_st_ref_get(v_a_4053_);
v_env_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc_ref(v_env_4062_);
lean_dec(v___x_4061_);
v___x_4063_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4064_ = lean_ctor_get(v___x_4063_, 0);
v_exportEntriesFn_4065_ = lean_ctor_get(v___x_4063_, 4);
v_asyncMode_4066_ = lean_ctor_get(v_toEnvExtension_4064_, 2);
v___x_4067_ = lean_box(0);
v___x_4068_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4056_, v_toEnvExtension_4064_, v_env_4058_, v_asyncMode_4066_, v___x_4067_);
v_importedEntries_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; 
v_unused_4122_ = lean_ctor_get(v___x_4068_, 1);
lean_dec(v_unused_4122_);
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4121_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_importedEntries_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4121_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v_exported_4075_; lean_object* v___x_4076_; size_t v_sz_4077_; size_t v___x_4078_; lean_object* v___x_4079_; 
v___x_4073_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4055_, v___x_4063_, v_env_4062_, v_asyncMode_4066_, v___x_4067_);
lean_inc_ref(v_exportEntriesFn_4065_);
v___x_4074_ = lean_apply_2(v_exportEntriesFn_4065_, v_env_4060_, v___x_4073_);
v_exported_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_exported_4075_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = lean_array_push(v_importedEntries_4069_, v_exported_4075_);
v_sz_4077_ = lean_array_size(v___x_4076_);
v___x_4078_ = ((size_t)0ULL);
v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_4076_, v_sz_4077_, v___x_4078_, v___x_4055_, v_a_4052_, v_a_4053_);
lean_dec_ref(v___x_4076_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; lean_object* v_a_4082_; lean_object* v___x_4083_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_4053_);
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref(v___x_4081_);
v___x_4083_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_4052_, v_a_4053_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v___x_4085_ = lean_box(0);
v___x_4086_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_4082_, v_a_4080_, v_a_4084_, v___x_4085_, v_a_4052_, v_a_4053_);
lean_dec(v_a_4080_);
lean_dec(v_a_4082_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4092_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
v___x_4088_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_4089_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_4090_ = l_Lean_MessageData_joinSep(v_a_4087_, v___x_4089_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set_tag(v___x_4071_, 7);
lean_ctor_set(v___x_4071_, 1, v___x_4090_);
lean_ctor_set(v___x_4071_, 0, v___x_4089_);
v___x_4092_ = v___x_4071_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4093_ = l_Lean_MessageData_nestD(v___x_4092_);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4088_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_4094_, v_a_4052_, v_a_4053_);
return v___x_4095_;
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_del_object(v___x_4071_);
v_a_4097_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4086_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4086_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_a_4082_);
lean_dec(v_a_4080_);
lean_del_object(v___x_4071_);
v_a_4105_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4083_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4083_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_del_object(v___x_4071_);
v_a_4113_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4079_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4079_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4123_, v_a_4124_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4128_, v_a_4129_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4132_, v_a_4133_, v_a_4134_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v___stx_4132_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_4137_, lean_object* v_t_4138_, lean_object* v_k_4139_, lean_object* v_fallback_4140_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4138_, v_k_4139_, v_fallback_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_4142_, lean_object* v_t_4143_, lean_object* v_k_4144_, lean_object* v_fallback_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_4142_, v_t_4143_, v_k_4144_, v_fallback_4145_);
lean_dec(v_fallback_4145_);
lean_dec(v_k_4144_);
lean_dec(v_t_4143_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_4147_, size_t v_sz_4148_, size_t v_i_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4147_, v_sz_4148_, v_i_4149_, v_b_4150_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_4155_, lean_object* v_sz_4156_, lean_object* v_i_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
size_t v_sz_boxed_4162_; size_t v_i_boxed_4163_; lean_object* v_res_4164_; 
v_sz_boxed_4162_ = lean_unbox_usize(v_sz_4156_);
lean_dec(v_sz_4156_);
v_i_boxed_4163_ = lean_unbox_usize(v_i_4157_);
lean_dec(v_i_4157_);
v_res_4164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4155_, v_sz_boxed_4162_, v_i_boxed_4163_, v_b_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec_ref(v_as_4155_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_4173_, lean_object* v___x_4174_, lean_object* v___x_4175_, lean_object* v_inst_4176_, lean_object* v_R_4177_, lean_object* v_a_4178_, lean_object* v_b_4179_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_4173_, v___x_4174_, v___x_4175_, v_a_4178_, v_b_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v_inst_4184_, lean_object* v_R_4185_, lean_object* v_a_4186_, lean_object* v_b_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_4181_, v___x_4182_, v___x_4183_, v_inst_4184_, v_R_4185_, v_a_4186_, v_b_4187_);
lean_dec_ref(v___x_4182_);
lean_dec_ref(v_val_4181_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_4189_, lean_object* v_t_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_4189_, v_t_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_4192_, lean_object* v_as_4193_, lean_object* v_lo_4194_, lean_object* v_hi_4195_, lean_object* v_w_4196_, lean_object* v_hlo_4197_, lean_object* v_hhi_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_4192_, v_as_4193_, v_lo_4194_, v_hi_4195_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_4200_, lean_object* v_as_4201_, lean_object* v_lo_4202_, lean_object* v_hi_4203_, lean_object* v_w_4204_, lean_object* v_hlo_4205_, lean_object* v_hhi_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_4200_, v_as_4201_, v_lo_4202_, v_hi_4203_, v_w_4204_, v_hlo_4205_, v_hhi_4206_);
lean_dec(v_hi_4203_);
lean_dec(v_n_4200_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_4208_, lean_object* v_x_4209_, lean_object* v_x_4210_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_4209_, v_x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4212_, lean_object* v_x_4213_, lean_object* v_x_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_4212_, v_x_4213_, v_x_4214_);
lean_dec(v_x_4214_);
lean_dec_ref(v_x_4213_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_4216_, v___y_4218_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_4226_, lean_object* v_t_4227_, lean_object* v_k_4228_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_4227_, v_k_4228_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_4230_, lean_object* v_t_4231_, lean_object* v_k_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_4230_, v_t_4231_, v_k_4232_);
lean_dec(v_k_4232_);
lean_dec(v_t_4231_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_4234_, lean_object* v_x_4235_, lean_object* v_x_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_4235_, v_x_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_4238_, lean_object* v_x_4239_, lean_object* v_x_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_4238_, v_x_4239_, v_x_4240_);
lean_dec(v_x_4240_);
lean_dec_ref(v_x_4239_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_4242_, lean_object* v_lo_4243_, lean_object* v_hi_4244_, lean_object* v_hhi_4245_, lean_object* v_pivot_4246_, lean_object* v_as_4247_, lean_object* v_i_4248_, lean_object* v_k_4249_, lean_object* v_ilo_4250_, lean_object* v_ik_4251_, lean_object* v_w_4252_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_4244_, v_pivot_4246_, v_as_4247_, v_i_4248_, v_k_4249_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_4254_, lean_object* v_lo_4255_, lean_object* v_hi_4256_, lean_object* v_hhi_4257_, lean_object* v_pivot_4258_, lean_object* v_as_4259_, lean_object* v_i_4260_, lean_object* v_k_4261_, lean_object* v_ilo_4262_, lean_object* v_ik_4263_, lean_object* v_w_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_4254_, v_lo_4255_, v_hi_4256_, v_hhi_4257_, v_pivot_4258_, v_as_4259_, v_i_4260_, v_k_4261_, v_ilo_4262_, v_ik_4263_, v_w_4264_);
lean_dec(v_hi_4256_);
lean_dec(v_lo_4255_);
lean_dec(v_n_4254_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_4266_, size_t v_sz_4267_, size_t v_i_4268_, lean_object* v_b_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4266_, v_sz_4267_, v_i_4268_, v_b_4269_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_4274_, lean_object* v_sz_4275_, lean_object* v_i_4276_, lean_object* v_b_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
size_t v_sz_boxed_4281_; size_t v_i_boxed_4282_; lean_object* v_res_4283_; 
v_sz_boxed_4281_ = lean_unbox_usize(v_sz_4275_);
lean_dec(v_sz_4275_);
v_i_boxed_4282_ = lean_unbox_usize(v_i_4276_);
lean_dec(v_i_4276_);
v_res_4283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4274_, v_sz_boxed_4281_, v_i_boxed_4282_, v_b_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v_as_4274_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_4284_, lean_object* v_t_4285_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4284_, v_t_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_4287_, lean_object* v_t_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_4287_, v_t_4288_);
lean_dec(v_t_4288_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_4290_, lean_object* v_as_4291_, lean_object* v_lo_4292_, lean_object* v_hi_4293_, lean_object* v_w_4294_, lean_object* v_hlo_4295_, lean_object* v_hhi_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4290_, v_as_4291_, v_lo_4292_, v_hi_4293_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_4298_, lean_object* v_as_4299_, lean_object* v_lo_4300_, lean_object* v_hi_4301_, lean_object* v_w_4302_, lean_object* v_hlo_4303_, lean_object* v_hhi_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_4298_, v_as_4299_, v_lo_4300_, v_hi_4301_, v_w_4302_, v_hlo_4303_, v_hhi_4304_);
lean_dec(v_hi_4301_);
lean_dec(v_n_4298_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4306_, v_x_4307_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_4312_, lean_object* v_x_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4312_, v_x_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_4318_, lean_object* v_x_4319_, size_t v_x_4320_, lean_object* v_x_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_4319_, v_x_4320_, v_x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4323_, lean_object* v_x_4324_, lean_object* v_x_4325_, lean_object* v_x_4326_){
_start:
{
size_t v_x_18973__boxed_4327_; lean_object* v_res_4328_; 
v_x_18973__boxed_4327_ = lean_unbox_usize(v_x_4325_);
lean_dec(v_x_4325_);
v_res_4328_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_4323_, v_x_4324_, v_x_18973__boxed_4327_, v_x_4326_);
lean_dec(v_x_4326_);
lean_dec_ref(v_x_4324_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_4329_, lean_object* v_k_4330_, lean_object* v_x_4331_, lean_object* v_x_4332_, lean_object* v_x_4333_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_4329_, v_k_4330_, v_x_4331_, v_x_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_4335_, lean_object* v_k_4336_, lean_object* v_x_4337_, lean_object* v_x_4338_, lean_object* v_x_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_4335_, v_k_4336_, v_x_4337_, v_x_4338_, v_x_4339_);
lean_dec_ref(v_k_4336_);
lean_dec_ref(v_as_4335_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_4341_, lean_object* v_m_4342_, lean_object* v_a_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_4342_, v_a_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_4345_, lean_object* v_m_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_4345_, v_m_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_m_4346_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_4349_, lean_object* v_lo_4350_, lean_object* v_hi_4351_, lean_object* v_hhi_4352_, lean_object* v_pivot_4353_, lean_object* v_as_4354_, lean_object* v_i_4355_, lean_object* v_k_4356_, lean_object* v_ilo_4357_, lean_object* v_ik_4358_, lean_object* v_w_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4351_, v_pivot_4353_, v_as_4354_, v_i_4355_, v_k_4356_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_4361_, lean_object* v_lo_4362_, lean_object* v_hi_4363_, lean_object* v_hhi_4364_, lean_object* v_pivot_4365_, lean_object* v_as_4366_, lean_object* v_i_4367_, lean_object* v_k_4368_, lean_object* v_ilo_4369_, lean_object* v_ik_4370_, lean_object* v_w_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_4361_, v_lo_4362_, v_hi_4363_, v_hhi_4364_, v_pivot_4365_, v_as_4366_, v_i_4367_, v_k_4368_, v_ilo_4369_, v_ik_4370_, v_w_4371_);
lean_dec(v_hi_4363_);
lean_dec(v_lo_4362_);
lean_dec(v_n_4361_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_4373_, lean_object* v_keys_4374_, lean_object* v_vals_4375_, lean_object* v_heq_4376_, lean_object* v_i_4377_, lean_object* v_k_4378_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_4374_, v_vals_4375_, v_i_4377_, v_k_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_4380_, lean_object* v_keys_4381_, lean_object* v_vals_4382_, lean_object* v_heq_4383_, lean_object* v_i_4384_, lean_object* v_k_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_4380_, v_keys_4381_, v_vals_4382_, v_heq_4383_, v_i_4384_, v_k_4385_);
lean_dec(v_k_4385_);
lean_dec_ref(v_vals_4382_);
lean_dec_ref(v_keys_4381_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_4387_, lean_object* v_a_4388_, lean_object* v_x_4389_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_4388_, v_x_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_4391_, lean_object* v_a_4392_, lean_object* v_x_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_4391_, v_a_4392_, v_x_4393_);
lean_dec(v_x_4393_);
lean_dec(v_a_4392_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4409_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_4411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4412_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_4413_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4409_, v___x_4410_, v___x_4411_, v___x_4412_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_4420_ = l_Lean_addBuiltinDocString(v___x_4418_, v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_4451_ = l_Lean_addBuiltinDeclarationRanges(v___x_4449_, v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_4454_, lean_object* v___x_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, uint8_t v_includeUnnamed_4458_, lean_object* v_x_4459_, lean_object* v_____s_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v_fst_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4521_; 
v_fst_4466_ = lean_ctor_get(v_x_4459_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_x_4459_);
if (v_isSharedCheck_4521_ == 0)
{
lean_object* v_unused_4522_; 
v_unused_4522_ = lean_ctor_get(v_x_4459_, 1);
lean_dec(v_unused_4522_);
v___x_4468_ = v_x_4459_;
v_isShared_4469_ = v_isSharedCheck_4521_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_fst_4466_);
lean_dec(v_x_4459_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4521_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v_userName_4471_; lean_object* v___y_4472_; lean_object* v___x_4506_; 
lean_inc(v_fst_4466_);
lean_inc_ref(v_env_4454_);
v___x_4506_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4454_, v_fst_4466_);
if (lean_obj_tag(v___x_4506_) == 1)
{
lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4514_; 
lean_del_object(v___x_4468_);
lean_dec(v_fst_4466_);
lean_dec(v___x_4455_);
lean_dec_ref(v_env_4454_);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; 
v_unused_4515_ = lean_ctor_get(v___x_4506_, 0);
lean_dec(v_unused_4515_);
v___x_4508_ = v___x_4506_;
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
else
{
lean_dec(v___x_4506_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v_____s_4460_);
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_____s_4460_);
v___x_4511_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
}
else
{
lean_object* v___x_4516_; 
lean_dec(v___x_4506_);
v___x_4516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_4457_, v_fst_4466_);
if (lean_obj_tag(v___x_4516_) == 1)
{
lean_object* v_val_4517_; 
v_val_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_val_4517_);
lean_dec_ref_known(v___x_4516_, 1);
v_userName_4471_ = v_val_4517_;
v___y_4472_ = v___y_4463_;
goto v___jp_4470_;
}
else
{
lean_dec(v___x_4516_);
if (v_includeUnnamed_4458_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_del_object(v___x_4468_);
lean_dec(v_fst_4466_);
lean_dec(v___x_4455_);
lean_dec_ref(v_env_4454_);
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_____s_4460_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; 
lean_inc(v_fst_4466_);
v___x_4520_ = l_Lean_Name_toString(v_fst_4466_, v_includeUnnamed_4458_);
v_userName_4471_ = v___x_4520_;
v___y_4472_ = v___y_4463_;
goto v___jp_4470_;
}
}
}
v___jp_4470_:
{
lean_object* v_ref_4473_; uint8_t v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v_ref_4473_ = lean_ctor_get(v___y_4472_, 2);
v___x_4474_ = 1;
v___x_4475_ = l_Lean_Options_empty;
v___x_4476_ = lean_box(0);
lean_inc(v_fst_4466_);
lean_inc_ref(v_env_4454_);
v___x_4477_ = l_Lean_findDocString_x3f(v_env_4454_, v_fst_4466_, v___x_4474_, v___x_4475_, v___x_4455_, v___x_4476_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4491_; 
lean_del_object(v___x_4468_);
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4491_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4491_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4482_ = l_Lean_NameSet_empty;
v___x_4483_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_4456_, v_fst_4466_, v___x_4482_);
lean_inc(v_fst_4466_);
v___x_4484_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_4454_, v_fst_4466_);
v___x_4485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4485_, 0, v_fst_4466_);
lean_ctor_set(v___x_4485_, 1, v_userName_4471_);
lean_ctor_set(v___x_4485_, 2, v___x_4483_);
lean_ctor_set(v___x_4485_, 3, v_a_4478_);
lean_ctor_set(v___x_4485_, 4, v___x_4484_);
v___x_4486_ = lean_array_push(v_____s_4460_, v___x_4485_);
v___x_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4487_);
v___x_4489_ = v___x_4480_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4505_; 
lean_dec_ref(v_userName_4471_);
lean_dec(v_fst_4466_);
lean_dec_ref(v_____s_4460_);
lean_dec_ref(v_env_4454_);
v_a_4492_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4494_ = v___x_4477_;
v_isShared_4495_ = v_isSharedCheck_4505_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4477_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4505_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4496_ = lean_io_error_to_string(v_a_4492_);
v___x_4497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
v___x_4498_ = l_Lean_MessageData_ofFormat(v___x_4497_);
lean_inc(v_ref_4473_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 1, v___x_4498_);
lean_ctor_set(v___x_4468_, 0, v_ref_4473_);
v___x_4500_ = v___x_4468_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_ref_4473_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4502_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4500_);
v___x_4502_ = v___x_4494_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_4523_, lean_object* v___x_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_includeUnnamed_4527_, lean_object* v_x_4528_, lean_object* v_____s_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
uint8_t v_includeUnnamed_boxed_4535_; lean_object* v_res_4536_; 
v_includeUnnamed_boxed_4535_ = lean_unbox(v_includeUnnamed_4527_);
v_res_4536_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4523_, v___x_4524_, v_a_4525_, v_a_4526_, v_includeUnnamed_boxed_4535_, v_x_4528_, v_____s_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v_a_4526_);
lean_dec(v_a_4525_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_b_4540_){
_start:
{
uint8_t v___x_4542_; 
v___x_4542_ = lean_usize_dec_lt(v_i_4539_, v_sz_4538_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_b_4540_);
return v___x_4543_;
}
else
{
lean_object* v_a_4544_; lean_object* v_fst_4545_; lean_object* v_snd_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; size_t v___x_4551_; size_t v___x_4552_; 
v_a_4544_ = lean_array_uget_borrowed(v_as_4537_, v_i_4539_);
v_fst_4545_ = lean_ctor_get(v_a_4544_, 0);
v_snd_4546_ = lean_ctor_get(v_a_4544_, 1);
v___x_4547_ = l_Lean_NameSet_empty;
v___x_4548_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4540_, v_fst_4545_, v___x_4547_);
lean_inc(v_snd_4546_);
v___x_4549_ = l_Lean_NameSet_insert(v___x_4548_, v_snd_4546_);
lean_inc(v_fst_4545_);
v___x_4550_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4545_, v___x_4549_, v_b_4540_);
v___x_4551_ = ((size_t)1ULL);
v___x_4552_ = lean_usize_add(v_i_4539_, v___x_4551_);
v_i_4539_ = v___x_4552_;
v_b_4540_ = v___x_4550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_4554_, lean_object* v_sz_4555_, lean_object* v_i_4556_, lean_object* v_b_4557_, lean_object* v___y_4558_){
_start:
{
size_t v_sz_boxed_4559_; size_t v_i_boxed_4560_; lean_object* v_res_4561_; 
v_sz_boxed_4559_ = lean_unbox_usize(v_sz_4555_);
lean_dec(v_sz_4555_);
v_i_boxed_4560_ = lean_unbox_usize(v_i_4556_);
lean_dec(v_i_4556_);
v_res_4561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4554_, v_sz_boxed_4559_, v_i_boxed_4560_, v_b_4557_);
lean_dec_ref(v_as_4554_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_4562_, size_t v_sz_4563_, size_t v_i_4564_, lean_object* v_b_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
uint8_t v___x_4571_; 
v___x_4571_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v_b_4565_);
return v___x_4572_;
}
else
{
lean_object* v_a_4573_; size_t v_sz_4574_; size_t v___x_4575_; lean_object* v___x_4576_; 
v_a_4573_ = lean_array_uget_borrowed(v_as_4562_, v_i_4564_);
v_sz_4574_ = lean_array_size(v_a_4573_);
v___x_4575_ = ((size_t)0ULL);
v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_4573_, v_sz_4574_, v___x_4575_, v_b_4565_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; size_t v___x_4578_; size_t v___x_4579_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref_known(v___x_4576_, 1);
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4564_, v___x_4578_);
v_i_4564_ = v___x_4579_;
v_b_4565_ = v_a_4577_;
goto _start;
}
else
{
return v___x_4576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_4581_, lean_object* v_sz_4582_, lean_object* v_i_4583_, lean_object* v_b_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
size_t v_sz_boxed_4590_; size_t v_i_boxed_4591_; lean_object* v_res_4592_; 
v_sz_boxed_4590_ = lean_unbox_usize(v_sz_4582_);
lean_dec(v_sz_4582_);
v_i_boxed_4591_ = lean_unbox_usize(v_i_4583_);
lean_dec(v_i_4583_);
v_res_4592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4581_, v_sz_boxed_4590_, v_i_boxed_4591_, v_b_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v_as_4581_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_4593_, lean_object* v_keys_4594_, lean_object* v_vals_4595_, lean_object* v_i_4596_, lean_object* v_acc_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4603_ = lean_array_get_size(v_keys_4594_);
v___x_4604_ = lean_nat_dec_lt(v_i_4596_, v___x_4603_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
lean_dec(v_i_4596_);
lean_dec_ref(v_f_4593_);
v___x_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4605_, 0, v_acc_4597_);
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
return v___x_4606_;
}
else
{
lean_object* v_k_4607_; lean_object* v_v_4608_; lean_object* v___x_4609_; 
v_k_4607_ = lean_array_fget_borrowed(v_keys_4594_, v_i_4596_);
v_v_4608_ = lean_array_fget_borrowed(v_vals_4595_, v_i_4596_);
lean_inc_ref(v_f_4593_);
lean_inc(v___y_4601_);
lean_inc_ref(v___y_4600_);
lean_inc(v___y_4599_);
lean_inc_ref(v___y_4598_);
lean_inc(v_v_4608_);
lean_inc(v_k_4607_);
v___x_4609_ = lean_apply_8(v_f_4593_, v_acc_4597_, v_k_4607_, v_v_4608_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, lean_box(0));
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
if (lean_obj_tag(v_a_4610_) == 0)
{
lean_dec_ref_known(v_a_4610_, 1);
lean_dec(v_i_4596_);
lean_dec_ref(v_f_4593_);
return v___x_4609_;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
lean_dec_ref_known(v___x_4609_, 1);
v_a_4611_ = lean_ctor_get(v_a_4610_, 0);
lean_inc(v_a_4611_);
lean_dec_ref_known(v_a_4610_, 1);
v___x_4612_ = lean_unsigned_to_nat(1u);
v___x_4613_ = lean_nat_add(v_i_4596_, v___x_4612_);
lean_dec(v_i_4596_);
v_i_4596_ = v___x_4613_;
v_acc_4597_ = v_a_4611_;
goto _start;
}
}
else
{
lean_dec(v_i_4596_);
lean_dec_ref(v_f_4593_);
return v___x_4609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_4615_, lean_object* v_keys_4616_, lean_object* v_vals_4617_, lean_object* v_i_4618_, lean_object* v_acc_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4615_, v_keys_4616_, v_vals_4617_, v_i_4618_, v_acc_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec_ref(v_vals_4617_);
lean_dec_ref(v_keys_4616_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_4626_, lean_object* v_as_4627_, size_t v_i_4628_, size_t v_stop_4629_, lean_object* v_b_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_a_4637_; lean_object* v___y_4642_; uint8_t v___x_4645_; 
v___x_4645_ = lean_usize_dec_eq(v_i_4628_, v_stop_4629_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; 
v___x_4646_ = lean_array_uget_borrowed(v_as_4627_, v_i_4628_);
switch(lean_obj_tag(v___x_4646_))
{
case 0:
{
lean_object* v_key_4647_; lean_object* v_val_4648_; lean_object* v___x_4649_; 
v_key_4647_ = lean_ctor_get(v___x_4646_, 0);
v_val_4648_ = lean_ctor_get(v___x_4646_, 1);
lean_inc_ref(v_f_4626_);
lean_inc(v___y_4634_);
lean_inc_ref(v___y_4633_);
lean_inc(v___y_4632_);
lean_inc_ref(v___y_4631_);
lean_inc(v_val_4648_);
lean_inc(v_key_4647_);
v___x_4649_ = lean_apply_8(v_f_4626_, v_b_4630_, v_key_4647_, v_val_4648_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, lean_box(0));
v___y_4642_ = v___x_4649_;
goto v___jp_4641_;
}
case 1:
{
lean_object* v_node_4650_; lean_object* v___x_4651_; 
v_node_4650_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_node_4650_);
lean_inc_ref(v_f_4626_);
v___x_4651_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4626_, v_node_4650_, v_b_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
v___y_4642_ = v___x_4651_;
goto v___jp_4641_;
}
default: 
{
v_a_4637_ = v_b_4630_;
goto v___jp_4636_;
}
}
}
else
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
lean_dec_ref(v_f_4626_);
v___x_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_b_4630_);
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
v___jp_4636_:
{
size_t v___x_4638_; size_t v___x_4639_; 
v___x_4638_ = ((size_t)1ULL);
v___x_4639_ = lean_usize_add(v_i_4628_, v___x_4638_);
v_i_4628_ = v___x_4639_;
v_b_4630_ = v_a_4637_;
goto _start;
}
v___jp_4641_:
{
if (lean_obj_tag(v___y_4642_) == 0)
{
lean_object* v_a_4643_; 
v_a_4643_ = lean_ctor_get(v___y_4642_, 0);
if (lean_obj_tag(v_a_4643_) == 0)
{
lean_dec_ref(v_f_4626_);
return v___y_4642_;
}
else
{
lean_object* v_a_4644_; 
lean_inc_ref(v_a_4643_);
lean_dec_ref_known(v___y_4642_, 1);
v_a_4644_ = lean_ctor_get(v_a_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v_a_4643_, 1);
v_a_4637_ = v_a_4644_;
goto v___jp_4636_;
}
}
else
{
lean_dec_ref(v_f_4626_);
return v___y_4642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_4654_, lean_object* v_x_4655_, lean_object* v_x_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
if (lean_obj_tag(v_x_4655_) == 0)
{
lean_object* v_es_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4676_; 
v_es_4662_ = lean_ctor_get(v_x_4655_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_x_4655_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4664_ = v_x_4655_;
v_isShared_4665_ = v_isSharedCheck_4676_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_es_4662_);
lean_dec(v_x_4655_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4676_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4666_ = lean_unsigned_to_nat(0u);
v___x_4667_ = lean_array_get_size(v_es_4662_);
v___x_4668_ = lean_nat_dec_lt(v___x_4666_, v___x_4667_);
if (v___x_4668_ == 0)
{
lean_object* v___x_4670_; 
lean_dec_ref(v_es_4662_);
lean_dec_ref(v_f_4654_);
if (v_isShared_4665_ == 0)
{
lean_ctor_set_tag(v___x_4664_, 1);
lean_ctor_set(v___x_4664_, 0, v_x_4656_);
v___x_4670_ = v___x_4664_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_x_4656_);
v___x_4670_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4671_; 
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
}
else
{
size_t v___x_4673_; size_t v___x_4674_; lean_object* v___x_4675_; 
lean_del_object(v___x_4664_);
v___x_4673_ = ((size_t)0ULL);
v___x_4674_ = lean_usize_of_nat(v___x_4667_);
v___x_4675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4654_, v_es_4662_, v___x_4673_, v___x_4674_, v_x_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec_ref(v_es_4662_);
return v___x_4675_;
}
}
}
else
{
lean_object* v_ks_4677_; lean_object* v_vs_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_ks_4677_ = lean_ctor_get(v_x_4655_, 0);
lean_inc_ref(v_ks_4677_);
v_vs_4678_ = lean_ctor_get(v_x_4655_, 1);
lean_inc_ref(v_vs_4678_);
lean_dec_ref_known(v_x_4655_, 2);
v___x_4679_ = lean_unsigned_to_nat(0u);
v___x_4680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4654_, v_ks_4677_, v_vs_4678_, v___x_4679_, v_x_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec_ref(v_vs_4678_);
lean_dec_ref(v_ks_4677_);
return v___x_4680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_4681_, lean_object* v_x_4682_, lean_object* v_x_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4681_, v_x_4682_, v_x_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_4690_, lean_object* v_as_4691_, lean_object* v_i_4692_, lean_object* v_stop_4693_, lean_object* v_b_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
size_t v_i_boxed_4700_; size_t v_stop_boxed_4701_; lean_object* v_res_4702_; 
v_i_boxed_4700_ = lean_unbox_usize(v_i_4692_);
lean_dec(v_i_4692_);
v_stop_boxed_4701_ = lean_unbox_usize(v_stop_4693_);
lean_dec(v_stop_4693_);
v_res_4702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4690_, v_as_4691_, v_i_boxed_4700_, v_stop_boxed_4701_, v_b_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec_ref(v_as_4691_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_4703_, lean_object* v_s_4704_, lean_object* v_a_4705_, lean_object* v_b_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4712_, 0, v_a_4705_);
lean_ctor_set(v___x_4712_, 1, v_b_4706_);
lean_inc(v___y_4710_);
lean_inc_ref(v___y_4709_);
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
v___x_4713_ = lean_apply_7(v_f_4703_, v___x_4712_, v_s_4704_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, lean_box(0));
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4740_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4716_ = v___x_4713_;
v_isShared_4717_ = v_isSharedCheck_4740_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4740_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
if (lean_obj_tag(v_a_4714_) == 0)
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4728_; 
v_a_4718_ = lean_ctor_get(v_a_4714_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v_a_4714_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4720_ = v_a_4714_;
v_isShared_4721_ = v_isSharedCheck_4728_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v_a_4714_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4728_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4723_);
v___x_4725_ = v___x_4716_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4739_; 
v_a_4729_ = lean_ctor_get(v_a_4714_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_a_4714_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4731_ = v_a_4714_;
v_isShared_4732_ = v_isSharedCheck_4739_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v_a_4714_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4739_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4736_; 
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4734_);
v___x_4736_ = v___x_4716_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v___x_4734_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
v_a_4741_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4713_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4713_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_4749_, lean_object* v_s_4750_, lean_object* v_a_4751_, lean_object* v_b_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_4749_, v_s_4750_, v_a_4751_, v_b_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_4759_, lean_object* v_init_4760_, lean_object* v_f_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v___f_4767_; lean_object* v___x_4768_; 
v___f_4767_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4767_, 0, v_f_4761_);
lean_inc_ref(v_map_4759_);
v___x_4768_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_4767_, v_map_4759_, v_init_4760_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4777_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4771_ = v___x_4768_;
v_isShared_4772_ = v_isSharedCheck_4777_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4768_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4777_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v_a_4773_; lean_object* v___x_4775_; 
v_a_4773_ = lean_ctor_get(v_a_4769_, 0);
lean_inc(v_a_4773_);
lean_dec(v_a_4769_);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v_a_4773_);
v___x_4775_ = v___x_4771_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
v_a_4778_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4768_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4768_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_4786_, lean_object* v_init_4787_, lean_object* v_f_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4786_, v_init_4787_, v_f_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
lean_dec_ref(v_map_4786_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_4795_){
_start:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v_env_4801_; lean_object* v___x_4802_; lean_object* v_ext_4803_; lean_object* v_toEnvExtension_4804_; lean_object* v_asyncMode_4805_; lean_object* v___x_4806_; lean_object* v_categories_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4797_ = lean_box(1);
v___x_4798_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4799_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4800_ = lean_st_ref_get(v___y_4795_);
v_env_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc_ref_n(v_env_4801_, 2);
lean_dec(v___x_4800_);
v___x_4802_ = l_Lean_Parser_parserExtension;
v_ext_4803_ = lean_ctor_get(v___x_4802_, 1);
v_toEnvExtension_4804_ = lean_ctor_get(v_ext_4803_, 0);
v_asyncMode_4805_ = lean_ctor_get(v_toEnvExtension_4804_, 2);
v___x_4806_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4799_, v___x_4802_, v_env_4801_, v_asyncMode_4805_);
v_categories_4807_ = lean_ctor_get(v___x_4806_, 2);
lean_inc_ref(v_categories_4807_);
lean_dec(v___x_4806_);
v___x_4808_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4809_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4807_, v___x_4808_);
lean_dec_ref(v_categories_4807_);
if (lean_obj_tag(v___x_4809_) == 1)
{
lean_object* v_val_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4841_; 
v_val_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4841_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_val_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4841_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___y_4815_; lean_object* v___x_4824_; lean_object* v_toEnvExtension_4825_; lean_object* v_exportEntriesFn_4826_; lean_object* v_asyncMode_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v_importedEntries_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v_exported_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4824_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4825_ = lean_ctor_get(v___x_4824_, 0);
v_exportEntriesFn_4826_ = lean_ctor_get(v___x_4824_, 4);
v_asyncMode_4827_ = lean_ctor_get(v_toEnvExtension_4825_, 2);
v___x_4828_ = lean_box(0);
lean_inc_ref_n(v_env_4801_, 2);
v___x_4829_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4798_, v_toEnvExtension_4825_, v_env_4801_, v_asyncMode_4827_, v___x_4828_);
v_importedEntries_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc_ref(v_importedEntries_4830_);
lean_dec(v___x_4829_);
v___x_4831_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4797_, v___x_4824_, v_env_4801_, v_asyncMode_4827_, v___x_4828_);
lean_inc_ref(v_exportEntriesFn_4826_);
v___x_4832_ = lean_apply_2(v_exportEntriesFn_4826_, v_env_4801_, v___x_4831_);
v_exported_4833_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_exported_4833_);
lean_dec_ref(v___x_4832_);
v___x_4834_ = lean_array_push(v_importedEntries_4830_, v_exported_4833_);
v___x_4835_ = lean_unsigned_to_nat(0u);
v___x_4836_ = lean_array_get_size(v___x_4834_);
v___x_4837_ = lean_nat_dec_lt(v___x_4835_, v___x_4836_);
if (v___x_4837_ == 0)
{
lean_dec_ref(v___x_4834_);
v___y_4815_ = v___x_4797_;
goto v___jp_4814_;
}
else
{
size_t v___x_4838_; size_t v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = ((size_t)0ULL);
v___x_4839_ = lean_usize_of_nat(v___x_4836_);
v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4834_, v___x_4838_, v___x_4839_, v___x_4797_);
lean_dec_ref(v___x_4834_);
v___y_4815_ = v___x_4840_;
goto v___jp_4814_;
}
v___jp_4814_:
{
lean_object* v_tables_4816_; lean_object* v_leadingTable_4817_; lean_object* v_trailingTable_4818_; lean_object* v_firstTokens_4819_; lean_object* v_firstTokens_4820_; lean_object* v___x_4822_; 
v_tables_4816_ = lean_ctor_get(v_val_4810_, 2);
v_leadingTable_4817_ = lean_ctor_get(v_tables_4816_, 0);
v_trailingTable_4818_ = lean_ctor_get(v_tables_4816_, 2);
lean_inc(v_trailingTable_4818_);
lean_inc(v_leadingTable_4817_);
lean_inc(v_val_4810_);
v_firstTokens_4819_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4810_, v_leadingTable_4817_, v___y_4815_);
v_firstTokens_4820_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4810_, v_trailingTable_4818_, v_firstTokens_4819_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set_tag(v___x_4812_, 0);
lean_ctor_set(v___x_4812_, 0, v_firstTokens_4820_);
v___x_4822_ = v___x_4812_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_firstTokens_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
else
{
lean_object* v___x_4842_; 
lean_dec(v___x_4809_);
lean_dec_ref(v_env_4801_);
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4797_);
return v___x_4842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4843_);
lean_dec(v___y_4843_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v_env_4858_; lean_object* v___x_4859_; lean_object* v_toEnvExtension_4860_; lean_object* v_exportEntriesFn_4861_; lean_object* v_asyncMode_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v_importedEntries_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v_exported_4868_; lean_object* v___x_4869_; size_t v_sz_4870_; size_t v___x_4871_; lean_object* v___x_4872_; 
v___x_4854_ = lean_box(1);
v___x_4855_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4856_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4857_ = lean_st_ref_get(v_a_4852_);
v_env_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc_ref_n(v_env_4858_, 4);
lean_dec(v___x_4857_);
v___x_4859_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4860_ = lean_ctor_get(v___x_4859_, 0);
v_exportEntriesFn_4861_ = lean_ctor_get(v___x_4859_, 4);
v_asyncMode_4862_ = lean_ctor_get(v_toEnvExtension_4860_, 2);
v___x_4863_ = lean_box(0);
v___x_4864_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4855_, v_toEnvExtension_4860_, v_env_4858_, v_asyncMode_4862_, v___x_4863_);
v_importedEntries_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc_ref(v_importedEntries_4865_);
lean_dec(v___x_4864_);
v___x_4866_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4854_, v___x_4859_, v_env_4858_, v_asyncMode_4862_, v___x_4863_);
lean_inc_ref(v_exportEntriesFn_4861_);
v___x_4867_ = lean_apply_2(v_exportEntriesFn_4861_, v_env_4858_, v___x_4866_);
v_exported_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_exported_4868_);
lean_dec_ref(v___x_4867_);
v___x_4869_ = lean_array_push(v_importedEntries_4865_, v_exported_4868_);
v_sz_4870_ = lean_array_size(v___x_4869_);
v___x_4871_ = ((size_t)0ULL);
v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_4869_, v_sz_4870_, v___x_4871_, v___x_4854_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
lean_dec_ref(v___x_4869_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4896_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4875_ = v___x_4872_;
v_isShared_4876_ = v_isSharedCheck_4896_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4872_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4896_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; lean_object* v_ext_4878_; lean_object* v_toEnvExtension_4879_; lean_object* v_asyncMode_4880_; lean_object* v___x_4881_; lean_object* v_categories_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4877_ = l_Lean_Parser_parserExtension;
v_ext_4878_ = lean_ctor_get(v___x_4877_, 1);
v_toEnvExtension_4879_ = lean_ctor_get(v_ext_4878_, 0);
v_asyncMode_4880_ = lean_ctor_get(v_toEnvExtension_4879_, 2);
lean_inc_ref(v_env_4858_);
v___x_4881_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4856_, v___x_4877_, v_env_4858_, v_asyncMode_4880_);
v_categories_4882_ = lean_ctor_get(v___x_4881_, 2);
lean_inc_ref(v_categories_4882_);
lean_dec(v___x_4881_);
v___x_4883_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4885_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4882_, v___x_4884_);
lean_dec_ref(v_categories_4882_);
if (lean_obj_tag(v___x_4885_) == 1)
{
lean_object* v_val_4886_; lean_object* v___x_4887_; lean_object* v_a_4888_; lean_object* v_kinds_4889_; lean_object* v___x_4890_; lean_object* v___f_4891_; lean_object* v___x_4892_; 
lean_del_object(v___x_4875_);
v_val_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_val_4886_);
lean_dec_ref_known(v___x_4885_, 1);
v___x_4887_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_4852_);
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref(v___x_4887_);
v_kinds_4889_ = lean_ctor_get(v_val_4886_, 1);
lean_inc_ref(v_kinds_4889_);
lean_dec(v_val_4886_);
v___x_4890_ = lean_box(v_includeUnnamed_4848_);
v___f_4891_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4891_, 0, v_env_4858_);
lean_closure_set(v___f_4891_, 1, v___x_4863_);
lean_closure_set(v___f_4891_, 2, v_a_4873_);
lean_closure_set(v___f_4891_, 3, v_a_4888_);
lean_closure_set(v___f_4891_, 4, v___x_4890_);
v___x_4892_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_4889_, v___x_4883_, v___f_4891_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
lean_dec_ref(v_kinds_4889_);
return v___x_4892_;
}
else
{
lean_object* v___x_4894_; 
lean_dec(v___x_4885_);
lean_dec(v_a_4873_);
lean_dec_ref(v_env_4858_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 0, v___x_4883_);
v___x_4894_ = v___x_4875_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4883_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
lean_dec_ref(v_env_4858_);
v_a_4897_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4872_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4872_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
uint8_t v_includeUnnamed_boxed_4911_; lean_object* v_res_4912_; 
v_includeUnnamed_boxed_4911_ = lean_unbox(v_includeUnnamed_4905_);
v_res_4912_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_4911_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_4913_, size_t v_sz_4914_, size_t v_i_4915_, lean_object* v_b_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4913_, v_sz_4914_, v_i_4915_, v_b_4916_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_4923_, lean_object* v_sz_4924_, lean_object* v_i_4925_, lean_object* v_b_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
size_t v_sz_boxed_4932_; size_t v_i_boxed_4933_; lean_object* v_res_4934_; 
v_sz_boxed_4932_ = lean_unbox_usize(v_sz_4924_);
lean_dec(v_sz_4924_);
v_i_boxed_4933_ = lean_unbox_usize(v_i_4925_);
lean_dec(v_i_4925_);
v_res_4934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_4923_, v_sz_boxed_4932_, v_i_boxed_4933_, v_b_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec_ref(v_as_4923_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v___x_4940_; 
v___x_4940_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4938_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_4947_, lean_object* v_00_u03b2_4948_, lean_object* v_map_4949_, lean_object* v_init_4950_, lean_object* v_f_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4949_, v_init_4950_, v_f_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_4958_, lean_object* v_00_u03b2_4959_, lean_object* v_map_4960_, lean_object* v_init_4961_, lean_object* v_f_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_4958_, v_00_u03b2_4959_, v_map_4960_, v_init_4961_, v_f_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec_ref(v_map_4960_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_4969_, lean_object* v_f_4970_, lean_object* v_init_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4970_, v_map_4969_, v_init_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_4978_, lean_object* v_f_4979_, lean_object* v_init_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_4978_, v_f_4979_, v_init_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_4987_, lean_object* v_00_u03c3_4988_, lean_object* v_00_u03b2_4989_, lean_object* v_map_4990_, lean_object* v_f_4991_, lean_object* v_init_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v___x_4998_; 
v___x_4998_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4991_, v_map_4990_, v_init_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
return v___x_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_4999_, lean_object* v_00_u03c3_5000_, lean_object* v_00_u03b2_5001_, lean_object* v_map_5002_, lean_object* v_f_5003_, lean_object* v_init_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_4999_, v_00_u03c3_5000_, v_00_u03b2_5001_, v_map_5002_, v_f_5003_, v_init_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec(v___y_5008_);
lean_dec_ref(v___y_5007_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_5011_, lean_object* v_00_u03c3_5012_, lean_object* v_00_u03b1_5013_, lean_object* v_00_u03b2_5014_, lean_object* v_f_5015_, lean_object* v_x_5016_, lean_object* v_x_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5015_, v_x_5016_, v_x_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_5024_, lean_object* v_00_u03c3_5025_, lean_object* v_00_u03b1_5026_, lean_object* v_00_u03b2_5027_, lean_object* v_f_5028_, lean_object* v_x_5029_, lean_object* v_x_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_5024_, v_00_u03c3_5025_, v_00_u03b1_5026_, v_00_u03b2_5027_, v_f_5028_, v_x_5029_, v_x_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_5037_, lean_object* v_00_u03b2_5038_, lean_object* v_00_u03c3_5039_, lean_object* v_00_u03c3_5040_, lean_object* v_f_5041_, lean_object* v_as_5042_, size_t v_i_5043_, size_t v_stop_5044_, lean_object* v_b_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5041_, v_as_5042_, v_i_5043_, v_stop_5044_, v_b_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5052_, lean_object* v_00_u03b2_5053_, lean_object* v_00_u03c3_5054_, lean_object* v_00_u03c3_5055_, lean_object* v_f_5056_, lean_object* v_as_5057_, lean_object* v_i_5058_, lean_object* v_stop_5059_, lean_object* v_b_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
size_t v_i_boxed_5066_; size_t v_stop_boxed_5067_; lean_object* v_res_5068_; 
v_i_boxed_5066_ = lean_unbox_usize(v_i_5058_);
lean_dec(v_i_5058_);
v_stop_boxed_5067_ = lean_unbox_usize(v_stop_5059_);
lean_dec(v_stop_5059_);
v_res_5068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_5052_, v_00_u03b2_5053_, v_00_u03c3_5054_, v_00_u03c3_5055_, v_f_5056_, v_as_5057_, v_i_boxed_5066_, v_stop_boxed_5067_, v_b_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
lean_dec_ref(v_as_5057_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_5069_, lean_object* v_00_u03c3_5070_, lean_object* v_00_u03b1_5071_, lean_object* v_00_u03b2_5072_, lean_object* v_f_5073_, lean_object* v_keys_5074_, lean_object* v_vals_5075_, lean_object* v_heq_5076_, lean_object* v_i_5077_, lean_object* v_acc_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_5073_, v_keys_5074_, v_vals_5075_, v_i_5077_, v_acc_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_5085_, lean_object* v_00_u03c3_5086_, lean_object* v_00_u03b1_5087_, lean_object* v_00_u03b2_5088_, lean_object* v_f_5089_, lean_object* v_keys_5090_, lean_object* v_vals_5091_, lean_object* v_heq_5092_, lean_object* v_i_5093_, lean_object* v_acc_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_){
_start:
{
lean_object* v_res_5100_; 
v_res_5100_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_5085_, v_00_u03c3_5086_, v_00_u03b1_5087_, v_00_u03b2_5088_, v_f_5089_, v_keys_5090_, v_vals_5091_, v_heq_5092_, v_i_5093_, v_acc_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec_ref(v_vals_5091_);
lean_dec_ref(v_keys_5090_);
return v_res_5100_;
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
