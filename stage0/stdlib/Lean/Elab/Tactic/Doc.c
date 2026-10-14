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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
size_t v_sz_boxed_53_; size_t v___x_6058__boxed_54_; lean_object* v_res_55_; 
v_sz_boxed_53_ = lean_unbox_usize(v_sz_46_);
lean_dec(v_sz_46_);
v___x_6058__boxed_54_ = lean_unbox_usize(v___x_47_);
lean_dec(v___x_47_);
v_res_55_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(v_x_45_, v_sz_boxed_53_, v___x_6058__boxed_54_, v_content_48_, v___y_49_, v___y_50_, v___y_51_);
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
size_t v_sz_boxed_625_; size_t v___x_6920__boxed_626_; lean_object* v_res_627_; 
v_sz_boxed_625_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v___x_6920__boxed_626_ = lean_unbox_usize(v___x_619_);
lean_dec(v___x_619_);
v_res_627_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(v_sz_boxed_625_, v___x_6920__boxed_626_, v_content_620_, v___y_621_, v___y_622_, v___y_623_);
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
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
lean_ctor_set(v___x_1209_, 2, v___x_1208_);
lean_ctor_set(v___x_1209_, 3, v___x_1208_);
lean_ctor_set(v___x_1209_, 4, v___x_1207_);
lean_ctor_set(v___x_1209_, 5, v___x_1207_);
lean_ctor_set(v___x_1209_, 6, v___x_1207_);
lean_ctor_set(v___x_1209_, 7, v___x_1207_);
lean_ctor_set(v___x_1209_, 8, v___x_1207_);
lean_ctor_set(v___x_1209_, 9, v___x_1207_);
lean_ctor_set(v___x_1209_, 10, v___x_1207_);
lean_ctor_set(v___x_1209_, 11, v___x_1206_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = lean_unsigned_to_nat(32u);
v___x_1211_ = lean_mk_empty_array_with_capacity(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1213_ = ((size_t)5ULL);
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_unsigned_to_nat(32u);
v___x_1216_ = lean_mk_empty_array_with_capacity(v___x_1215_);
v___x_1217_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3);
v___x_1218_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1216_);
lean_ctor_set(v___x_1218_, 2, v___x_1214_);
lean_ctor_set(v___x_1218_, 3, v___x_1214_);
lean_ctor_set_usize(v___x_1218_, 4, v___x_1213_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = lean_box(1);
v___x_1220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_1221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1220_);
lean_ctor_set(v___x_1222_, 2, v___x_1219_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_msgData_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v_env_1227_; uint8_t v___x_1228_; lean_object* v_env_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_scopes_1232_; lean_object* v___x_1233_; lean_object* v_opts_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1226_ = lean_st_ref_get(v___y_1224_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = 0;
v_env_1229_ = l_Lean_Environment_setRecordingDeps(v_env_1227_, v___x_1228_);
v___x_1230_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1231_ = lean_st_ref_get(v___y_1224_);
v_scopes_1232_ = lean_ctor_get(v___x_1231_, 2);
lean_inc(v_scopes_1232_);
lean_dec(v___x_1231_);
v___x_1233_ = l_List_head_x21___redArg(v___x_1230_, v_scopes_1232_);
lean_dec(v_scopes_1232_);
v_opts_1234_ = lean_ctor_get(v___x_1233_, 1);
lean_inc_ref(v_opts_1234_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2);
v___x_1236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5);
v___x_1237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1237_, 0, v_env_1229_);
lean_ctor_set(v___x_1237_, 1, v___x_1235_);
lean_ctor_set(v___x_1237_, 2, v___x_1236_);
lean_ctor_set(v___x_1237_, 3, v_opts_1234_);
v___x_1238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_msgData_1223_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_msgData_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1240_, v___y_1241_);
lean_dec(v___y_1241_);
return v_res_1243_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_box(1);
v___x_1245_ = l_Lean_MessageData_ofFormat(v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2));
v___x_1250_ = l_Lean_MessageData_ofFormat(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
return v_x_1251_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1276_; 
v_head_1253_ = lean_ctor_get(v_x_1252_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1252_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1256_ = v_x_1252_;
v_isShared_1257_ = v_isSharedCheck_1276_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_head_1253_);
lean_dec(v_x_1252_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1276_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_before_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1274_; 
v_before_1258_ = lean_ctor_get(v_head_1253_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_head_1253_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_head_1253_, 1);
lean_dec(v_unused_1275_);
v___x_1260_ = v_head_1253_;
v_isShared_1261_ = v_isSharedCheck_1274_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_before_1258_);
lean_dec(v_head_1253_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1274_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 7);
lean_ctor_set(v___x_1260_, 1, v___x_1262_);
lean_ctor_set(v___x_1260_, 0, v_x_1251_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_x_1251_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 7);
lean_ctor_set(v___x_1256_, 1, v___x_1265_);
lean_ctor_set(v___x_1256_, 0, v___x_1264_);
v___x_1267_ = v___x_1256_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = l_Lean_MessageData_ofSyntax(v_before_1258_);
v___x_1269_ = l_Lean_indentD(v___x_1268_);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1267_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v_x_1251_ = v___x_1270_;
v_x_1252_ = v_tail_1254_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(lean_object* v_opts_1277_, lean_object* v_opt_1278_){
_start:
{
lean_object* v_name_1279_; lean_object* v_defValue_1280_; lean_object* v_map_1281_; lean_object* v___x_1282_; 
v_name_1279_ = lean_ctor_get(v_opt_1278_, 0);
v_defValue_1280_ = lean_ctor_get(v_opt_1278_, 1);
v_map_1281_ = lean_ctor_get(v_opts_1277_, 0);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1281_, v_name_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_unbox(v_defValue_1280_);
return v___x_1283_;
}
else
{
lean_object* v_val_1284_; 
v_val_1284_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1284_);
lean_dec_ref_known(v___x_1282_, 1);
if (lean_obj_tag(v_val_1284_) == 1)
{
uint8_t v_v_1285_; 
v_v_1285_ = lean_ctor_get_uint8(v_val_1284_, 0);
lean_dec_ref_known(v_val_1284_, 0);
return v_v_1285_;
}
else
{
uint8_t v___x_1286_; 
lean_dec(v_val_1284_);
v___x_1286_ = lean_unbox(v_defValue_1280_);
return v___x_1286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17___boxed(lean_object* v_opts_1287_, lean_object* v_opt_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1287_, v_opt_1288_);
lean_dec_ref(v_opt_1288_);
lean_dec_ref(v_opts_1287_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1));
v___x_1295_ = l_Lean_MessageData_ofFormat(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_msgData_1296_, lean_object* v_macroStack_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_scopes_1302_; lean_object* v___x_1303_; lean_object* v_opts_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1300_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1301_ = lean_st_ref_get(v___y_1298_);
v_scopes_1302_ = lean_ctor_get(v___x_1301_, 2);
lean_inc(v_scopes_1302_);
lean_dec(v___x_1301_);
v___x_1303_ = l_List_head_x21___redArg(v___x_1300_, v_scopes_1302_);
lean_dec(v_scopes_1302_);
v_opts_1304_ = lean_ctor_get(v___x_1303_, 1);
lean_inc_ref(v_opts_1304_);
lean_dec(v___x_1303_);
v___x_1305_ = l_Lean_Elab_pp_macroStack;
v___x_1306_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1304_, v___x_1305_);
lean_dec_ref(v_opts_1304_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec(v_macroStack_1297_);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_msgData_1296_);
return v___x_1307_;
}
else
{
if (lean_obj_tag(v_macroStack_1297_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_msgData_1296_);
return v___x_1308_;
}
else
{
lean_object* v_head_1309_; lean_object* v_after_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1325_; 
v_head_1309_ = lean_ctor_get(v_macroStack_1297_, 0);
lean_inc(v_head_1309_);
v_after_1310_ = lean_ctor_get(v_head_1309_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_head_1309_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_head_1309_, 0);
lean_dec(v_unused_1326_);
v___x_1312_ = v_head_1309_;
v_isShared_1313_ = v_isSharedCheck_1325_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_after_1310_);
lean_dec(v_head_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1325_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 7);
lean_ctor_set(v___x_1312_, 1, v___x_1314_);
lean_ctor_set(v___x_1312_, 0, v_msgData_1296_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_msgData_1296_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_msgData_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1317_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_MessageData_ofSyntax(v_after_1310_);
v___x_1320_ = l_Lean_indentD(v___x_1319_);
v_msgData_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1321_, 0, v___x_1318_);
lean_ctor_set(v_msgData_1321_, 1, v___x_1320_);
v___x_1322_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(v_msgData_1321_, v_macroStack_1297_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_msgData_1327_, lean_object* v_macroStack_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1327_, v_macroStack_1328_, v___y_1329_);
lean_dec(v___y_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Elab_Command_getRef___redArg(v___y_1333_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v_macroStack_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v_macroStack_1338_ = lean_ctor_get(v___y_1333_, 4);
v___x_1339_ = l_Lean_Elab_getBetterRef(v_a_1337_, v_macroStack_1338_);
lean_dec(v_a_1337_);
v___x_1340_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msg_1332_, v___y_1334_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1340_);
lean_inc(v_macroStack_1338_);
v___x_1342_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_a_1341_, v_macroStack_1338_, v___y_1334_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1339_);
lean_ctor_set(v___x_1347_, 1, v_a_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 1);
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_msg_1332_);
v_a_1352_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1336_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1336_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object* v_ref_1365_, lean_object* v_msg_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Elab_Command_getRef___redArg(v___y_1367_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v_fileName_1372_; lean_object* v_fileMap_1373_; lean_object* v_currRecDepth_1374_; lean_object* v_cmdPos_1375_; lean_object* v_macroStack_1376_; lean_object* v_quotContext_x3f_1377_; lean_object* v_currMacroScope_1378_; lean_object* v_snap_x3f_1379_; lean_object* v_cancelTk_x3f_1380_; uint8_t v_suppressElabErrors_1381_; lean_object* v_ref_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v_fileName_1372_ = lean_ctor_get(v___y_1367_, 0);
v_fileMap_1373_ = lean_ctor_get(v___y_1367_, 1);
v_currRecDepth_1374_ = lean_ctor_get(v___y_1367_, 2);
v_cmdPos_1375_ = lean_ctor_get(v___y_1367_, 3);
v_macroStack_1376_ = lean_ctor_get(v___y_1367_, 4);
v_quotContext_x3f_1377_ = lean_ctor_get(v___y_1367_, 5);
v_currMacroScope_1378_ = lean_ctor_get(v___y_1367_, 6);
v_snap_x3f_1379_ = lean_ctor_get(v___y_1367_, 8);
v_cancelTk_x3f_1380_ = lean_ctor_get(v___y_1367_, 9);
v_suppressElabErrors_1381_ = lean_ctor_get_uint8(v___y_1367_, sizeof(void*)*10);
v_ref_1382_ = l_Lean_replaceRef(v_ref_1365_, v_a_1371_);
lean_dec(v_a_1371_);
lean_inc(v_cancelTk_x3f_1380_);
lean_inc(v_snap_x3f_1379_);
lean_inc(v_currMacroScope_1378_);
lean_inc(v_quotContext_x3f_1377_);
lean_inc(v_macroStack_1376_);
lean_inc(v_cmdPos_1375_);
lean_inc(v_currRecDepth_1374_);
lean_inc_ref(v_fileMap_1373_);
lean_inc_ref(v_fileName_1372_);
v___x_1383_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1383_, 0, v_fileName_1372_);
lean_ctor_set(v___x_1383_, 1, v_fileMap_1373_);
lean_ctor_set(v___x_1383_, 2, v_currRecDepth_1374_);
lean_ctor_set(v___x_1383_, 3, v_cmdPos_1375_);
lean_ctor_set(v___x_1383_, 4, v_macroStack_1376_);
lean_ctor_set(v___x_1383_, 5, v_quotContext_x3f_1377_);
lean_ctor_set(v___x_1383_, 6, v_currMacroScope_1378_);
lean_ctor_set(v___x_1383_, 7, v_ref_1382_);
lean_ctor_set(v___x_1383_, 8, v_snap_x3f_1379_);
lean_ctor_set(v___x_1383_, 9, v_cancelTk_x3f_1380_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*10, v_suppressElabErrors_1381_);
v___x_1384_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1366_, v___x_1383_, v___y_1368_);
lean_dec_ref_known(v___x_1383_, 10);
return v___x_1384_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_msg_1366_);
v_a_1385_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1370_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1370_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object* v_ref_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1393_, v_msg_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v_ref_1393_);
return v_res_1398_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0));
v___x_1401_ = l_Lean_stringToMessageData(v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object* v_stx_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = l_Lean_Syntax_getArg(v_stx_1406_, v___x_1416_);
if (lean_obj_tag(v___x_1417_) == 1)
{
lean_object* v_kind_1418_; 
v_kind_1418_ = lean_ctor_get(v___x_1417_, 1);
lean_inc(v_kind_1418_);
if (lean_obj_tag(v_kind_1418_) == 1)
{
lean_object* v_pre_1419_; 
v_pre_1419_ = lean_ctor_get(v_kind_1418_, 0);
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
lean_inc(v_pre_1421_);
if (lean_obj_tag(v_pre_1421_) == 1)
{
lean_object* v_pre_1422_; 
v_pre_1422_ = lean_ctor_get(v_pre_1421_, 0);
if (lean_obj_tag(v_pre_1422_) == 0)
{
lean_object* v_args_1423_; lean_object* v_str_1424_; lean_object* v_str_1425_; lean_object* v_str_1426_; lean_object* v_str_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_args_1423_ = lean_ctor_get(v___x_1417_, 2);
lean_inc_ref(v_args_1423_);
lean_dec_ref_known(v___x_1417_, 3);
v_str_1424_ = lean_ctor_get(v_kind_1418_, 1);
lean_inc_ref(v_str_1424_);
lean_dec_ref_known(v_kind_1418_, 2);
v_str_1425_ = lean_ctor_get(v_pre_1419_, 1);
lean_inc_ref(v_str_1425_);
lean_dec_ref_known(v_pre_1419_, 2);
v_str_1426_ = lean_ctor_get(v_pre_1420_, 1);
lean_inc_ref(v_str_1426_);
lean_dec_ref_known(v_pre_1420_, 2);
v_str_1427_ = lean_ctor_get(v_pre_1421_, 1);
lean_inc_ref(v_str_1427_);
lean_dec_ref_known(v_pre_1421_, 2);
v___x_1428_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2));
v___x_1429_ = lean_string_dec_eq(v_str_1427_, v___x_1428_);
lean_dec_ref(v_str_1427_);
if (v___x_1429_ == 0)
{
lean_dec_ref(v_str_1426_);
lean_dec_ref(v_str_1425_);
lean_dec_ref(v_str_1424_);
lean_dec_ref(v_args_1423_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3));
v___x_1431_ = lean_string_dec_eq(v_str_1426_, v___x_1430_);
lean_dec_ref(v_str_1426_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v_str_1425_);
lean_dec_ref(v_str_1424_);
lean_dec_ref(v_args_1423_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4));
v___x_1433_ = lean_string_dec_eq(v_str_1425_, v___x_1432_);
lean_dec_ref(v_str_1425_);
if (v___x_1433_ == 0)
{
lean_dec_ref(v_str_1424_);
lean_dec_ref(v_args_1423_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5));
v___x_1435_ = lean_string_dec_eq(v_str_1424_, v___x_1434_);
lean_dec_ref(v_str_1424_);
if (v___x_1435_ == 0)
{
lean_dec_ref(v_args_1423_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = lean_array_get_size(v_args_1423_);
v___x_1437_ = lean_unsigned_to_nat(2u);
v___x_1438_ = lean_nat_dec_eq(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_dec_ref(v_args_1423_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_array_fget(v_args_1423_, v___x_1439_);
lean_dec_ref(v_args_1423_);
if (lean_obj_tag(v___x_1440_) == 2)
{
lean_object* v_val_1441_; lean_object* v___x_1442_; 
lean_dec(v_stx_1406_);
v_val_1441_ = lean_ctor_get(v___x_1440_, 1);
lean_inc_ref(v_val_1441_);
lean_dec_ref_known(v___x_1440_, 2);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_val_1441_);
return v___x_1442_;
}
else
{
lean_dec(v___x_1440_);
goto v___jp_1410_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1421_, 2);
lean_dec_ref_known(v_pre_1420_, 2);
lean_dec_ref_known(v_pre_1419_, 2);
lean_dec_ref_known(v_kind_1418_, 2);
lean_dec_ref_known(v___x_1417_, 3);
goto v___jp_1410_;
}
}
else
{
lean_dec(v_pre_1421_);
lean_dec_ref_known(v_pre_1420_, 2);
lean_dec_ref_known(v_pre_1419_, 2);
lean_dec_ref_known(v_kind_1418_, 2);
lean_dec_ref_known(v___x_1417_, 3);
goto v___jp_1410_;
}
}
else
{
lean_dec_ref_known(v_pre_1419_, 2);
lean_dec(v_pre_1420_);
lean_dec_ref_known(v_kind_1418_, 2);
lean_dec_ref_known(v___x_1417_, 3);
goto v___jp_1410_;
}
}
else
{
lean_dec(v_pre_1419_);
lean_dec_ref_known(v_kind_1418_, 2);
lean_dec_ref_known(v___x_1417_, 3);
goto v___jp_1410_;
}
}
else
{
lean_dec_ref_known(v___x_1417_, 3);
lean_dec(v_kind_1418_);
goto v___jp_1410_;
}
}
else
{
lean_dec(v___x_1417_);
goto v___jp_1410_;
}
v___jp_1410_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1);
lean_inc(v_stx_1406_);
v___x_1412_ = l_Lean_MessageData_ofSyntax(v_stx_1406_);
v___x_1413_ = l_Lean_indentD(v___x_1412_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1411_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_stx_1406_, v___x_1414_, v___y_1407_, v___y_1408_);
lean_dec(v_stx_1406_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object* v_stx_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_stx_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object* v_doc_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = l_Lean_isVersoDocComment(v_doc_1448_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_doc_1448_, v_a_1449_, v_a_1450_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___boxed), 4, 1);
lean_closure_set(v___x_1454_, 0, v_doc_1448_);
v___x_1455_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1454_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1486_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1486_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1486_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
if (lean_obj_tag(v_a_1456_) == 1)
{
lean_object* v_val_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_del_object(v___x_1458_);
v_val_1460_ = lean_ctor_get(v_a_1456_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v_a_1456_, 1);
v___x_1461_ = l_Lean_TSyntax_getVersoBlocks(v_val_1460_);
lean_dec(v_val_1460_);
v___x_1462_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1462_, 0, v___x_1461_);
v___x_1463_ = 0;
v___x_1464_ = lean_box(v___x_1463_);
v___x_1465_ = lean_alloc_closure((void*)(l_Lean_Doc_DocM_execForModule___boxed), 10, 3);
lean_closure_set(v___x_1465_, 0, lean_box(0));
lean_closure_set(v___x_1465_, 1, v___x_1462_);
lean_closure_set(v___x_1465_, 2, v___x_1464_);
v___x_1466_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1465_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_fst_1468_; lean_object* v_fst_1469_; lean_object* v_snd_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_fst_1468_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_fst_1468_);
lean_dec(v_a_1467_);
v_fst_1469_ = lean_ctor_get(v_fst_1468_, 0);
lean_inc(v_fst_1469_);
v_snd_1470_ = lean_ctor_get(v_fst_1468_, 1);
lean_inc(v_snd_1470_);
lean_dec(v_fst_1468_);
v___f_1471_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1471_, 0, v_fst_1469_);
lean_closure_set(v___f_1471_, 1, v_snd_1470_);
v___x_1472_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_1472_, 0, v___f_1471_);
v___x_1473_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1472_, v_a_1449_, v_a_1450_);
return v___x_1473_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1466_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1466_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_dec(v_a_1456_);
v___x_1482_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1482_);
v___x_1484_ = v___x_1458_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1455_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1455_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object* v_doc_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_doc_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object* v_p_1500_, lean_object* v_level_1501_, lean_object* v_part_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1501_, v_part_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object* v_p_1508_, lean_object* v_level_1509_, lean_object* v_part_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(v_p_1508_, v_level_1509_, v_part_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec(v_level_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object* v_00_u03b1_1516_, lean_object* v_ref_1517_, lean_object* v_msg_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1517_, v_msg_1518_, v___y_1519_, v___y_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_ref_1524_, lean_object* v_msg_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(v_00_u03b1_1523_, v_ref_1524_, v_msg_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v_ref_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(lean_object* v_p_1530_, lean_object* v___x_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_bs_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1531_, v_sz_1532_, v_i_1533_, v_bs_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___boxed(lean_object* v_p_1540_, lean_object* v___x_1541_, lean_object* v_sz_1542_, lean_object* v_i_1543_, lean_object* v_bs_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
size_t v_sz_boxed_1549_; size_t v_i_boxed_1550_; lean_object* v_res_1551_; 
v_sz_boxed_1549_ = lean_unbox_usize(v_sz_1542_);
lean_dec(v_sz_1542_);
v_i_boxed_1550_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(v_p_1540_, v___x_1541_, v_sz_boxed_1549_, v_i_boxed_1550_, v_bs_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___x_1541_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(lean_object* v_msgData_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1552_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(v_msgData_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1562_, lean_object* v_msg_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1563_, v___y_1564_, v___y_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1568_, lean_object* v_msg_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(v_00_u03b1_1568_, v_msg_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(lean_object* v_msgData_1574_, lean_object* v_macroStack_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1574_, v_macroStack_1575_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_msgData_1580_, lean_object* v_macroStack_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(v_msgData_1580_, v_macroStack_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1586_, lean_object* v___x_1587_, lean_object* v_s_1588_){
_start:
{
lean_object* v_addEntryFn_1589_; lean_object* v_importedEntries_1590_; lean_object* v_state_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_addEntryFn_1589_ = lean_ctor_get(v___x_1586_, 3);
lean_inc(v_addEntryFn_1589_);
lean_dec_ref(v___x_1586_);
v_importedEntries_1590_ = lean_ctor_get(v_s_1588_, 0);
v_state_1591_ = lean_ctor_get(v_s_1588_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_s_1588_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v_s_1588_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_state_1591_);
lean_inc(v_importedEntries_1590_);
lean_dec(v_s_1588_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_state_1595_; lean_object* v___x_1597_; 
v_state_1595_ = lean_apply_2(v_addEntryFn_1589_, v_state_1591_, v___x_1587_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v_state_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_importedEntries_1590_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_state_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1600_, v___x_1601_, v___y_1606_, v___y_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed(lean_object* v___x_1610_, lean_object* v___x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(v___x_1610_, v___x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1619_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_1628_ = l_Lean_stringToMessageData(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_messages_1655_; lean_object* v_scopes_1656_; lean_object* v_usedQuotCtxts_1657_; lean_object* v_nextMacroScope_1658_; lean_object* v_maxRecDepth_1659_; lean_object* v_ngen_1660_; lean_object* v_auxDeclNGen_1661_; lean_object* v_infoState_1662_; lean_object* v_traceState_1663_; lean_object* v_snapshotTasks_1664_; lean_object* v_prevLinterStates_1665_; lean_object* v_codeQualityEntryTasks_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
lean_inc(v_x_1650_);
v___x_1674_ = l_Lean_Syntax_isOfKind(v_x_1650_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v_x_1650_);
v___x_1675_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1676_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1675_, v_a_1651_, v_a_1652_);
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = l_Lean_Syntax_getArg(v_x_1650_, v___x_1677_);
lean_inc(v___x_1678_);
v___x_1679_ = l_Lean_Syntax_matchesNull(v___x_1678_, v___x_1677_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1678_);
v___x_1681_ = l_Lean_Syntax_matchesNull(v___x_1678_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v___x_1678_);
lean_dec(v_x_1650_);
v___x_1682_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1683_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1682_, v_a_1651_, v_a_1652_);
return v___x_1683_;
}
else
{
lean_object* v_docs_1684_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1744_; 
v_docs_1684_ = l_Lean_Syntax_getArg(v___x_1678_, v___x_1677_);
lean_dec(v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_docs_1684_);
v___x_1778_ = l_Lean_Syntax_isOfKind(v_docs_1684_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_docs_1684_);
lean_dec(v_x_1650_);
v___x_1779_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1780_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1779_, v_a_1651_, v_a_1652_);
return v___x_1780_;
}
else
{
goto v___jp_1770_;
}
}
else
{
goto v___jp_1770_;
}
v___jp_1685_:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_docs_1684_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v_env_1692_; lean_object* v_messages_1693_; lean_object* v_scopes_1694_; lean_object* v_usedQuotCtxts_1695_; lean_object* v_nextMacroScope_1696_; lean_object* v_maxRecDepth_1697_; lean_object* v_ngen_1698_; lean_object* v_auxDeclNGen_1699_; lean_object* v_infoState_1700_; lean_object* v_traceState_1701_; lean_object* v_snapshotTasks_1702_; lean_object* v_prevLinterStates_1703_; lean_object* v_codeQualityEntryTasks_1704_; lean_object* v___x_1705_; lean_object* v_toEnvExtension_1706_; lean_object* v_asyncMode_1707_; uint8_t v_logWrites_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1691_ = lean_st_ref_take(v___y_1688_);
v_env_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc_ref(v_env_1692_);
v_messages_1693_ = lean_ctor_get(v___x_1691_, 1);
lean_inc_ref(v_messages_1693_);
v_scopes_1694_ = lean_ctor_get(v___x_1691_, 2);
lean_inc(v_scopes_1694_);
v_usedQuotCtxts_1695_ = lean_ctor_get(v___x_1691_, 3);
lean_inc(v_usedQuotCtxts_1695_);
v_nextMacroScope_1696_ = lean_ctor_get(v___x_1691_, 4);
lean_inc(v_nextMacroScope_1696_);
v_maxRecDepth_1697_ = lean_ctor_get(v___x_1691_, 5);
lean_inc(v_maxRecDepth_1697_);
v_ngen_1698_ = lean_ctor_get(v___x_1691_, 6);
lean_inc_ref(v_ngen_1698_);
v_auxDeclNGen_1699_ = lean_ctor_get(v___x_1691_, 7);
lean_inc_ref(v_auxDeclNGen_1699_);
v_infoState_1700_ = lean_ctor_get(v___x_1691_, 8);
lean_inc_ref(v_infoState_1700_);
v_traceState_1701_ = lean_ctor_get(v___x_1691_, 9);
lean_inc_ref(v_traceState_1701_);
v_snapshotTasks_1702_ = lean_ctor_get(v___x_1691_, 10);
lean_inc_ref(v_snapshotTasks_1702_);
v_prevLinterStates_1703_ = lean_ctor_get(v___x_1691_, 11);
lean_inc(v_prevLinterStates_1703_);
v_codeQualityEntryTasks_1704_ = lean_ctor_get(v___x_1691_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1704_);
lean_dec(v___x_1691_);
v___x_1705_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_1706_ = lean_ctor_get(v___x_1705_, 0);
v_asyncMode_1707_ = lean_ctor_get(v_toEnvExtension_1706_, 2);
v_logWrites_1708_ = lean_ctor_get_uint8(v_toEnvExtension_1706_, sizeof(void*)*6);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___y_1686_);
lean_ctor_set(v___x_1709_, 1, v_a_1690_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0), 3, 2);
lean_closure_set(v___f_1710_, 0, v___x_1705_);
lean_closure_set(v___f_1710_, 1, v___x_1709_);
v___x_1711_ = lean_box(0);
if (v_logWrites_1708_ == 0)
{
lean_object* v___x_1712_; 
lean_inc_ref(v_toEnvExtension_1706_);
v___x_1712_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1706_, v_env_1692_, v___f_1710_, v_asyncMode_1707_, v___x_1711_, v___x_1681_);
v_messages_1655_ = v_messages_1693_;
v_scopes_1656_ = v_scopes_1694_;
v_usedQuotCtxts_1657_ = v_usedQuotCtxts_1695_;
v_nextMacroScope_1658_ = v_nextMacroScope_1696_;
v_maxRecDepth_1659_ = v_maxRecDepth_1697_;
v_ngen_1660_ = v_ngen_1698_;
v_auxDeclNGen_1661_ = v_auxDeclNGen_1699_;
v_infoState_1662_ = v_infoState_1700_;
v_traceState_1663_ = v_traceState_1701_;
v_snapshotTasks_1664_ = v_snapshotTasks_1702_;
v_prevLinterStates_1665_ = v_prevLinterStates_1703_;
v_codeQualityEntryTasks_1666_ = v_codeQualityEntryTasks_1704_;
v___y_1667_ = v___y_1688_;
v___y_1668_ = v___x_1712_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_inc_ref_n(v_toEnvExtension_1706_, 2);
v___x_1713_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1706_, v_env_1692_);
lean_dec_ref(v_env_1692_);
v___x_1714_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1706_, v___x_1713_, v___f_1710_, v_asyncMode_1707_, v___x_1711_, v___x_1681_);
v_messages_1655_ = v_messages_1693_;
v_scopes_1656_ = v_scopes_1694_;
v_usedQuotCtxts_1657_ = v_usedQuotCtxts_1695_;
v_nextMacroScope_1658_ = v_nextMacroScope_1696_;
v_maxRecDepth_1659_ = v_maxRecDepth_1697_;
v_ngen_1660_ = v_ngen_1698_;
v_auxDeclNGen_1661_ = v_auxDeclNGen_1699_;
v_infoState_1662_ = v_infoState_1700_;
v_traceState_1663_ = v_traceState_1701_;
v_snapshotTasks_1664_ = v_snapshotTasks_1702_;
v_prevLinterStates_1665_ = v_prevLinterStates_1703_;
v_codeQualityEntryTasks_1666_ = v_codeQualityEntryTasks_1704_;
v___y_1667_ = v___y_1688_;
v___y_1668_ = v___x_1714_;
goto v___jp_1654_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v___y_1686_);
v_a_1715_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1689_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1689_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
v___jp_1723_:
{
if (v___y_1728_ == 0)
{
lean_dec(v___y_1725_);
v___y_1686_ = v___y_1726_;
v___y_1687_ = v___y_1724_;
v___y_1688_ = v___y_1727_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v_docs_1684_);
v___x_1729_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1730_ = l_Lean_MessageData_ofConstName(v___y_1726_, v___x_1679_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1725_, v___x_1733_, v___y_1724_, v___y_1727_);
lean_dec(v___y_1725_);
return v___x_1734_;
}
}
v___jp_1735_:
{
lean_object* v___x_1740_; lean_object* v_env_1741_; uint8_t v___x_1742_; 
v___x_1740_ = lean_st_ref_get(v___y_1739_);
v_env_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc_ref(v_env_1741_);
lean_dec(v___x_1740_);
v___x_1742_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1741_, v___y_1737_);
if (v___x_1742_ == 0)
{
v___y_1724_ = v___y_1738_;
v___y_1725_ = v___y_1736_;
v___y_1726_ = v___y_1737_;
v___y_1727_ = v___y_1739_;
v___y_1728_ = v___x_1681_;
goto v___jp_1723_;
}
else
{
v___y_1724_ = v___y_1738_;
v___y_1725_ = v___y_1736_;
v___y_1726_ = v___y_1737_;
v___y_1727_ = v___y_1739_;
v___y_1728_ = v___x_1679_;
goto v___jp_1723_;
}
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___f_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_box(0);
lean_inc(v___y_1744_);
v___f_1746_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1746_, 0, v___y_1744_);
lean_closure_set(v___f_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1746_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v_env_1750_; lean_object* v___x_1751_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc_n(v_a_1748_, 2);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_st_ref_get(v_a_1652_);
v_env_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc_ref(v_env_1750_);
lean_dec(v___x_1749_);
v___x_1751_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1750_, v_a_1748_);
if (lean_obj_tag(v___x_1751_) == 1)
{
lean_object* v_val_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_docs_1684_);
v_val_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1754_ = l_Lean_MessageData_ofConstName(v_a_1748_, v___x_1679_);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_MessageData_ofConstName(v_val_1752_, v___x_1679_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1753_);
v___x_1761_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1744_, v___x_1760_, v_a_1651_, v_a_1652_);
lean_dec(v___y_1744_);
return v___x_1761_;
}
else
{
lean_dec(v___x_1751_);
v___y_1736_ = v___y_1744_;
v___y_1737_ = v_a_1748_;
v___y_1738_ = v_a_1651_;
v___y_1739_ = v_a_1652_;
goto v___jp_1735_;
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v___y_1744_);
lean_dec(v_docs_1684_);
v_a_1762_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1747_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1747_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
v___jp_1770_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_unsigned_to_nat(2u);
v___x_1772_ = l_Lean_Syntax_getArg(v_x_1650_, v___x_1771_);
lean_dec(v_x_1650_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v___x_1772_);
v___x_1774_ = l_Lean_Syntax_isOfKind(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1772_);
lean_dec(v_docs_1684_);
v___x_1775_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1776_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1775_, v_a_1651_, v_a_1652_);
return v___x_1776_;
}
else
{
v___y_1744_ = v___x_1772_;
goto v___jp_1743_;
}
}
else
{
v___y_1744_ = v___x_1772_;
goto v___jp_1743_;
}
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v_cmd_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v___x_1678_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v_cmd_1782_ = l_Lean_Syntax_getArg(v_x_1650_, v___x_1781_);
lean_dec(v_x_1650_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15);
v___x_1784_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_cmd_1782_, v___x_1783_, v_a_1651_, v_a_1652_);
lean_dec(v_cmd_1782_);
return v___x_1784_;
}
}
v___jp_1654_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1668_);
lean_ctor_set(v___x_1669_, 1, v_messages_1655_);
lean_ctor_set(v___x_1669_, 2, v_scopes_1656_);
lean_ctor_set(v___x_1669_, 3, v_usedQuotCtxts_1657_);
lean_ctor_set(v___x_1669_, 4, v_nextMacroScope_1658_);
lean_ctor_set(v___x_1669_, 5, v_maxRecDepth_1659_);
lean_ctor_set(v___x_1669_, 6, v_ngen_1660_);
lean_ctor_set(v___x_1669_, 7, v_auxDeclNGen_1661_);
lean_ctor_set(v___x_1669_, 8, v_infoState_1662_);
lean_ctor_set(v___x_1669_, 9, v_traceState_1663_);
lean_ctor_set(v___x_1669_, 10, v_snapshotTasks_1664_);
lean_ctor_set(v___x_1669_, 11, v_prevLinterStates_1665_);
lean_ctor_set(v___x_1669_, 12, v_codeQualityEntryTasks_1666_);
v___x_1670_ = lean_st_ref_put(v___y_1667_, v___x_1669_);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1801_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_1803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1804_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_1805_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_1836_ = l_Lean_addBuiltinDeclarationRanges(v___x_1834_, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0(lean_object* v___x_1839_, lean_object* v___x_1840_, lean_object* v_s_1841_){
_start:
{
lean_object* v_addEntryFn_1842_; lean_object* v_importedEntries_1843_; lean_object* v_state_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_addEntryFn_1842_ = lean_ctor_get(v___x_1839_, 3);
lean_inc(v_addEntryFn_1842_);
lean_dec_ref(v___x_1839_);
v_importedEntries_1843_ = lean_ctor_get(v_s_1841_, 0);
v_state_1844_ = lean_ctor_get(v_s_1841_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_s_1841_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v_s_1841_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_state_1844_);
lean_inc(v_importedEntries_1843_);
lean_dec(v_s_1841_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_state_1848_; lean_object* v___x_1850_; 
v_state_1848_ = lean_apply_2(v_addEntryFn_1842_, v_state_1844_, v___x_1840_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v_state_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_importedEntries_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_state_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2));
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v_messages_1872_; lean_object* v_scopes_1873_; lean_object* v_usedQuotCtxts_1874_; lean_object* v_nextMacroScope_1875_; lean_object* v_maxRecDepth_1876_; lean_object* v_ngen_1877_; lean_object* v_auxDeclNGen_1878_; lean_object* v_infoState_1879_; lean_object* v_traceState_1880_; lean_object* v_snapshotTasks_1881_; lean_object* v_prevLinterStates_1882_; lean_object* v_codeQualityEntryTasks_1883_; lean_object* v___y_1884_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v_a_1894_; lean_object* v_doc_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; 
v___x_1888_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
lean_inc(v_x_1865_);
v___x_1889_ = l_Lean_Syntax_isOfKind(v_x_1865_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec(v_x_1865_);
v___x_1958_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1959_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1958_, v_a_1866_, v_a_1867_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = l_Lean_Syntax_getArg(v_x_1865_, v___x_1960_);
v___x_1962_ = l_Lean_Syntax_isNone(v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1961_);
v___x_1964_ = l_Lean_Syntax_matchesNull(v___x_1961_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec(v___x_1961_);
lean_dec(v_x_1865_);
v___x_1965_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1966_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1965_, v_a_1866_, v_a_1867_);
return v___x_1966_;
}
else
{
lean_object* v_doc_1967_; 
v_doc_1967_ = l_Lean_Syntax_getArg(v___x_1961_, v___x_1960_);
lean_dec(v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_doc_1967_);
v___x_1971_ = l_Lean_Syntax_isOfKind(v_doc_1967_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v_doc_1967_);
lean_dec(v_x_1865_);
v___x_1972_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1973_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1972_, v_a_1866_, v_a_1867_);
return v___x_1973_;
}
else
{
goto v___jp_1968_;
}
}
else
{
goto v___jp_1968_;
}
v___jp_1968_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_doc_1967_);
v_doc_1924_ = v___x_1969_;
v___y_1925_ = v_a_1866_;
v___y_1926_ = v_a_1867_;
goto v___jp_1923_;
}
}
}
else
{
lean_object* v___x_1974_; 
lean_dec(v___x_1961_);
v___x_1974_ = lean_box(0);
v_doc_1924_ = v___x_1974_;
v___y_1925_ = v_a_1866_;
v___y_1926_ = v_a_1867_;
goto v___jp_1923_;
}
}
v___jp_1869_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1885_, 0, v___y_1884_);
lean_ctor_set(v___x_1885_, 1, v_messages_1872_);
lean_ctor_set(v___x_1885_, 2, v_scopes_1873_);
lean_ctor_set(v___x_1885_, 3, v_usedQuotCtxts_1874_);
lean_ctor_set(v___x_1885_, 4, v_nextMacroScope_1875_);
lean_ctor_set(v___x_1885_, 5, v_maxRecDepth_1876_);
lean_ctor_set(v___x_1885_, 6, v_ngen_1877_);
lean_ctor_set(v___x_1885_, 7, v_auxDeclNGen_1878_);
lean_ctor_set(v___x_1885_, 8, v_infoState_1879_);
lean_ctor_set(v___x_1885_, 9, v_traceState_1880_);
lean_ctor_set(v___x_1885_, 10, v_snapshotTasks_1881_);
lean_ctor_set(v___x_1885_, 11, v_prevLinterStates_1882_);
lean_ctor_set(v___x_1885_, 12, v_codeQualityEntryTasks_1883_);
v___x_1886_ = lean_st_ref_put(v___y_1871_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___y_1870_);
return v___x_1887_;
}
v___jp_1890_:
{
lean_object* v___x_1895_; lean_object* v_env_1896_; lean_object* v_messages_1897_; lean_object* v_scopes_1898_; lean_object* v_usedQuotCtxts_1899_; lean_object* v_nextMacroScope_1900_; lean_object* v_maxRecDepth_1901_; lean_object* v_ngen_1902_; lean_object* v_auxDeclNGen_1903_; lean_object* v_infoState_1904_; lean_object* v_traceState_1905_; lean_object* v_snapshotTasks_1906_; lean_object* v_prevLinterStates_1907_; lean_object* v_codeQualityEntryTasks_1908_; lean_object* v___x_1909_; lean_object* v_toEnvExtension_1910_; lean_object* v_asyncMode_1911_; uint8_t v_logWrites_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; 
v___x_1895_ = lean_st_ref_take(v___y_1893_);
v_env_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc_ref(v_env_1896_);
v_messages_1897_ = lean_ctor_get(v___x_1895_, 1);
lean_inc_ref(v_messages_1897_);
v_scopes_1898_ = lean_ctor_get(v___x_1895_, 2);
lean_inc(v_scopes_1898_);
v_usedQuotCtxts_1899_ = lean_ctor_get(v___x_1895_, 3);
lean_inc(v_usedQuotCtxts_1899_);
v_nextMacroScope_1900_ = lean_ctor_get(v___x_1895_, 4);
lean_inc(v_nextMacroScope_1900_);
v_maxRecDepth_1901_ = lean_ctor_get(v___x_1895_, 5);
lean_inc(v_maxRecDepth_1901_);
v_ngen_1902_ = lean_ctor_get(v___x_1895_, 6);
lean_inc_ref(v_ngen_1902_);
v_auxDeclNGen_1903_ = lean_ctor_get(v___x_1895_, 7);
lean_inc_ref(v_auxDeclNGen_1903_);
v_infoState_1904_ = lean_ctor_get(v___x_1895_, 8);
lean_inc_ref(v_infoState_1904_);
v_traceState_1905_ = lean_ctor_get(v___x_1895_, 9);
lean_inc_ref(v_traceState_1905_);
v_snapshotTasks_1906_ = lean_ctor_get(v___x_1895_, 10);
lean_inc_ref(v_snapshotTasks_1906_);
v_prevLinterStates_1907_ = lean_ctor_get(v___x_1895_, 11);
lean_inc(v_prevLinterStates_1907_);
v_codeQualityEntryTasks_1908_ = lean_ctor_get(v___x_1895_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1908_);
lean_dec(v___x_1895_);
v___x_1909_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1910_ = lean_ctor_get(v___x_1909_, 0);
v_asyncMode_1911_ = lean_ctor_get(v_toEnvExtension_1910_, 2);
v_logWrites_1912_ = lean_ctor_get_uint8(v_toEnvExtension_1910_, sizeof(void*)*6);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_TSyntax_getId(v___y_1892_);
lean_dec(v___y_1892_);
v___x_1915_ = l_Lean_TSyntax_getString(v___y_1891_);
lean_dec(v___y_1891_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v_a_1894_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1914_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0), 3, 2);
lean_closure_set(v___f_1918_, 0, v___x_1909_);
lean_closure_set(v___f_1918_, 1, v___x_1917_);
v___x_1919_ = lean_box(0);
if (v_logWrites_1912_ == 0)
{
lean_object* v___x_1920_; 
lean_inc_ref(v_toEnvExtension_1910_);
v___x_1920_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1910_, v_env_1896_, v___f_1918_, v_asyncMode_1911_, v___x_1919_, v___x_1889_);
v___y_1870_ = v___x_1913_;
v___y_1871_ = v___y_1893_;
v_messages_1872_ = v_messages_1897_;
v_scopes_1873_ = v_scopes_1898_;
v_usedQuotCtxts_1874_ = v_usedQuotCtxts_1899_;
v_nextMacroScope_1875_ = v_nextMacroScope_1900_;
v_maxRecDepth_1876_ = v_maxRecDepth_1901_;
v_ngen_1877_ = v_ngen_1902_;
v_auxDeclNGen_1878_ = v_auxDeclNGen_1903_;
v_infoState_1879_ = v_infoState_1904_;
v_traceState_1880_ = v_traceState_1905_;
v_snapshotTasks_1881_ = v_snapshotTasks_1906_;
v_prevLinterStates_1882_ = v_prevLinterStates_1907_;
v_codeQualityEntryTasks_1883_ = v_codeQualityEntryTasks_1908_;
v___y_1884_ = v___x_1920_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_inc_ref_n(v_toEnvExtension_1910_, 2);
v___x_1921_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1910_, v_env_1896_);
lean_dec_ref(v_env_1896_);
v___x_1922_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1910_, v___x_1921_, v___f_1918_, v_asyncMode_1911_, v___x_1919_, v___x_1889_);
v___y_1870_ = v___x_1913_;
v___y_1871_ = v___y_1893_;
v_messages_1872_ = v_messages_1897_;
v_scopes_1873_ = v_scopes_1898_;
v_usedQuotCtxts_1874_ = v_usedQuotCtxts_1899_;
v_nextMacroScope_1875_ = v_nextMacroScope_1900_;
v_maxRecDepth_1876_ = v_maxRecDepth_1901_;
v_ngen_1877_ = v_ngen_1902_;
v_auxDeclNGen_1878_ = v_auxDeclNGen_1903_;
v_infoState_1879_ = v_infoState_1904_;
v_traceState_1880_ = v_traceState_1905_;
v_snapshotTasks_1881_ = v_snapshotTasks_1906_;
v_prevLinterStates_1882_ = v_prevLinterStates_1907_;
v_codeQualityEntryTasks_1883_ = v_codeQualityEntryTasks_1908_;
v___y_1884_ = v___x_1922_;
goto v___jp_1869_;
}
}
v___jp_1923_:
{
lean_object* v___x_1927_; lean_object* v_tag_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1927_ = lean_unsigned_to_nat(2u);
v_tag_1928_ = l_Lean_Syntax_getArg(v_x_1865_, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v_tag_1928_);
v___x_1930_ = l_Lean_Syntax_isOfKind(v_tag_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v_tag_1928_);
lean_dec(v_doc_1924_);
lean_dec(v_x_1865_);
v___x_1931_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1932_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1931_, v___y_1925_, v___y_1926_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v_user_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1933_ = lean_unsigned_to_nat(3u);
v_user_1934_ = l_Lean_Syntax_getArg(v_x_1865_, v___x_1933_);
lean_dec(v_x_1865_);
v___x_1935_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_user_1934_);
v___x_1936_ = l_Lean_Syntax_isOfKind(v_user_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec(v_user_1934_);
lean_dec(v_tag_1928_);
lean_dec(v_doc_1924_);
v___x_1937_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1938_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1937_, v___y_1925_, v___y_1926_);
return v___x_1938_;
}
else
{
if (lean_obj_tag(v_doc_1924_) == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_box(0);
v___y_1891_ = v_user_1934_;
v___y_1892_ = v_tag_1928_;
v___y_1893_ = v___y_1926_;
v_a_1894_ = v___x_1939_;
goto v___jp_1890_;
}
else
{
lean_object* v_val_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1957_; 
v_val_1940_ = lean_ctor_get(v_doc_1924_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_doc_1924_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1942_ = v_doc_1924_;
v_isShared_1943_ = v_isSharedCheck_1957_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_val_1940_);
lean_dec(v_doc_1924_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1957_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; 
v___x_1944_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_val_1940_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v_a_1945_);
v___x_1947_ = v___x_1942_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v___y_1891_ = v_user_1934_;
v___y_1892_ = v_tag_1928_;
v___y_1893_ = v___y_1926_;
v_a_1894_ = v___x_1947_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_del_object(v___x_1942_);
lean_dec(v_user_1934_);
lean_dec(v_tag_1928_);
v_a_1949_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1944_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1944_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_1975_, v_a_1976_, v_a_1977_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1988_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1989_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
v___x_1990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_1991_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_1992_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1988_, v___x_1989_, v___x_1990_, v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_2023_ = l_Lean_addBuiltinDeclarationRanges(v___x_2021_, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
return v___x_2028_;
}
else
{
lean_dec_ref(v___x_2026_);
lean_inc_ref(v_x_2027_);
return v_x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2029_, v_x_2030_);
lean_dec(v_x_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_2032_, lean_object* v_k_2033_, lean_object* v_t_2034_){
_start:
{
if (lean_obj_tag(v_t_2034_) == 0)
{
lean_object* v_size_2035_; lean_object* v_k_2036_; lean_object* v_v_2037_; lean_object* v_l_2038_; lean_object* v_r_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2365_; 
v_size_2035_ = lean_ctor_get(v_t_2034_, 0);
v_k_2036_ = lean_ctor_get(v_t_2034_, 1);
v_v_2037_ = lean_ctor_get(v_t_2034_, 2);
v_l_2038_ = lean_ctor_get(v_t_2034_, 3);
v_r_2039_ = lean_ctor_get(v_t_2034_, 4);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_t_2034_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2041_ = v_t_2034_;
v_isShared_2042_ = v_isSharedCheck_2365_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_r_2039_);
lean_inc(v_l_2038_);
lean_inc(v_v_2037_);
lean_inc(v_k_2036_);
lean_inc(v_size_2035_);
lean_dec(v_t_2034_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2365_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
uint8_t v___x_2043_; 
v___x_2043_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2033_, v_k_2036_);
switch(v___x_2043_)
{
case 0:
{
lean_object* v_impl_2044_; lean_object* v___x_2045_; 
lean_del_object(v___x_2041_);
lean_dec(v_size_2035_);
v_impl_2044_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2032_, v_k_2033_, v_l_2038_);
v___x_2045_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2036_, v_v_2037_, v_impl_2044_, v_r_2039_);
return v___x_2045_;
}
case 1:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v_k_2036_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_v_2037_);
v___x_2047_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2032_, v___x_2046_);
lean_dec_ref_known(v___x_2046_, 1);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_del_object(v___x_2041_);
lean_dec(v_size_2035_);
lean_dec(v_k_2033_);
if (lean_obj_tag(v_l_2038_) == 0)
{
if (lean_obj_tag(v_r_2039_) == 0)
{
lean_object* v_size_2048_; lean_object* v_k_2049_; lean_object* v_v_2050_; lean_object* v_l_2051_; lean_object* v_r_2052_; lean_object* v_size_2053_; lean_object* v_k_2054_; lean_object* v_v_2055_; lean_object* v_l_2056_; lean_object* v_r_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_size_2048_ = lean_ctor_get(v_l_2038_, 0);
v_k_2049_ = lean_ctor_get(v_l_2038_, 1);
v_v_2050_ = lean_ctor_get(v_l_2038_, 2);
v_l_2051_ = lean_ctor_get(v_l_2038_, 3);
v_r_2052_ = lean_ctor_get(v_l_2038_, 4);
lean_inc(v_r_2052_);
v_size_2053_ = lean_ctor_get(v_r_2039_, 0);
v_k_2054_ = lean_ctor_get(v_r_2039_, 1);
v_v_2055_ = lean_ctor_get(v_r_2039_, 2);
v_l_2056_ = lean_ctor_get(v_r_2039_, 3);
lean_inc(v_l_2056_);
v_r_2057_ = lean_ctor_get(v_r_2039_, 4);
v___x_2058_ = lean_unsigned_to_nat(1u);
v___x_2059_ = lean_nat_dec_lt(v_size_2048_, v_size_2053_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2195_; 
lean_inc(v_l_2051_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_l_2038_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; lean_object* v_unused_2197_; lean_object* v_unused_2198_; lean_object* v_unused_2199_; lean_object* v_unused_2200_; 
v_unused_2196_ = lean_ctor_get(v_l_2038_, 4);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_l_2038_, 3);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_l_2038_, 2);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_l_2038_, 1);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_l_2038_, 0);
lean_dec(v_unused_2200_);
v___x_2061_ = v_l_2038_;
v_isShared_2062_ = v_isSharedCheck_2195_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_l_2038_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2195_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v_tree_2064_; 
v___x_2063_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2049_, v_v_2050_, v_l_2051_, v_r_2052_);
v_tree_2064_ = lean_ctor_get(v___x_2063_, 2);
if (lean_obj_tag(v_tree_2064_) == 0)
{
lean_object* v_k_2065_; lean_object* v_v_2066_; lean_object* v_size_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
lean_inc_ref(v_tree_2064_);
v_k_2065_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_k_2065_);
v_v_2066_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_v_2066_);
lean_dec_ref(v___x_2063_);
v_size_2067_ = lean_ctor_get(v_tree_2064_, 0);
v___x_2068_ = lean_unsigned_to_nat(3u);
v___x_2069_ = lean_nat_mul(v___x_2068_, v_size_2067_);
v___x_2070_ = lean_nat_dec_lt(v___x_2069_, v_size_2053_);
lean_dec(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
lean_dec(v_l_2056_);
v___x_2071_ = lean_nat_add(v___x_2058_, v_size_2067_);
v___x_2072_ = lean_nat_add(v___x_2071_, v_size_2053_);
lean_dec(v___x_2071_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_r_2039_);
lean_ctor_set(v___x_2061_, 3, v_tree_2064_);
lean_ctor_set(v___x_2061_, 2, v_v_2066_);
lean_ctor_set(v___x_2061_, 1, v_k_2065_);
lean_ctor_set(v___x_2061_, 0, v___x_2072_);
v___x_2074_ = v___x_2061_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_tree_2064_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_r_2039_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2130_; 
lean_inc(v_r_2057_);
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
lean_inc(v_size_2053_);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_r_2039_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; lean_object* v_unused_2134_; lean_object* v_unused_2135_; 
v_unused_2131_ = lean_ctor_get(v_r_2039_, 4);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_r_2039_, 3);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_r_2039_, 2);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_r_2039_, 1);
lean_dec(v_unused_2134_);
v_unused_2135_ = lean_ctor_get(v_r_2039_, 0);
lean_dec(v_unused_2135_);
v___x_2077_ = v_r_2039_;
v_isShared_2078_ = v_isSharedCheck_2130_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v_r_2039_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2130_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_size_2079_; lean_object* v_k_2080_; lean_object* v_v_2081_; lean_object* v_l_2082_; lean_object* v_r_2083_; lean_object* v_size_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_size_2079_ = lean_ctor_get(v_l_2056_, 0);
v_k_2080_ = lean_ctor_get(v_l_2056_, 1);
v_v_2081_ = lean_ctor_get(v_l_2056_, 2);
v_l_2082_ = lean_ctor_get(v_l_2056_, 3);
v_r_2083_ = lean_ctor_get(v_l_2056_, 4);
v_size_2084_ = lean_ctor_get(v_r_2057_, 0);
v___x_2085_ = lean_unsigned_to_nat(2u);
v___x_2086_ = lean_nat_mul(v___x_2085_, v_size_2084_);
v___x_2087_ = lean_nat_dec_lt(v_size_2079_, v___x_2086_);
lean_dec(v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2115_; 
lean_inc(v_r_2083_);
lean_inc(v_l_2082_);
lean_inc(v_v_2081_);
lean_inc(v_k_2080_);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; lean_object* v_unused_2120_; 
v_unused_2116_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_l_2056_, 2);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_l_2056_, 1);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2120_);
v___x_2089_ = v_l_2056_;
v_isShared_2090_ = v_isSharedCheck_2115_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v_l_2056_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2115_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2105_; 
v___x_2091_ = lean_nat_add(v___x_2058_, v_size_2067_);
v___x_2092_ = lean_nat_add(v___x_2091_, v_size_2053_);
lean_dec(v_size_2053_);
if (lean_obj_tag(v_l_2082_) == 0)
{
lean_object* v_size_2113_; 
v_size_2113_ = lean_ctor_get(v_l_2082_, 0);
lean_inc(v_size_2113_);
v___y_2105_ = v_size_2113_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
v___y_2105_ = v___x_2114_;
goto v___jp_2104_;
}
v___jp_2093_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = lean_nat_add(v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_r_2057_);
lean_ctor_set(v___x_2089_, 3, v_r_2083_);
lean_ctor_set(v___x_2089_, 2, v_v_2055_);
lean_ctor_set(v___x_2089_, 1, v_k_2054_);
lean_ctor_set(v___x_2089_, 0, v___x_2097_);
v___x_2099_ = v___x_2089_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_r_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_2057_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 4, v___x_2099_);
lean_ctor_set(v___x_2077_, 3, v___y_2094_);
lean_ctor_set(v___x_2077_, 2, v_v_2081_);
lean_ctor_set(v___x_2077_, 1, v_k_2080_);
lean_ctor_set(v___x_2077_, 0, v___x_2092_);
v___x_2101_ = v___x_2077_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_2080_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_2081_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v___y_2094_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_nat_add(v___x_2091_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec(v___x_2091_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_l_2082_);
lean_ctor_set(v___x_2061_, 3, v_tree_2064_);
lean_ctor_set(v___x_2061_, 2, v_v_2066_);
lean_ctor_set(v___x_2061_, 1, v_k_2065_);
lean_ctor_set(v___x_2061_, 0, v___x_2106_);
v___x_2108_ = v___x_2061_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_tree_2064_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_l_2082_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_nat_add(v___x_2058_, v_size_2084_);
if (lean_obj_tag(v_r_2083_) == 0)
{
lean_object* v_size_2110_; 
v_size_2110_ = lean_ctor_get(v_r_2083_, 0);
lean_inc(v_size_2110_);
v___y_2094_ = v___x_2108_;
v___y_2095_ = v___x_2109_;
v___y_2096_ = v_size_2110_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___y_2094_ = v___x_2108_;
v___y_2095_ = v___x_2109_;
v___y_2096_ = v___x_2111_;
goto v___jp_2093_;
}
}
}
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2121_ = lean_nat_add(v___x_2058_, v_size_2067_);
v___x_2122_ = lean_nat_add(v___x_2121_, v_size_2053_);
lean_dec(v_size_2053_);
v___x_2123_ = lean_nat_add(v___x_2121_, v_size_2079_);
lean_dec(v___x_2121_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 4, v_l_2056_);
lean_ctor_set(v___x_2077_, 3, v_tree_2064_);
lean_ctor_set(v___x_2077_, 2, v_v_2066_);
lean_ctor_set(v___x_2077_, 1, v_k_2065_);
lean_ctor_set(v___x_2077_, 0, v___x_2123_);
v___x_2125_ = v___x_2077_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_tree_2064_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_l_2056_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_r_2057_);
lean_ctor_set(v___x_2061_, 3, v___x_2125_);
lean_ctor_set(v___x_2061_, 2, v_v_2055_);
lean_ctor_set(v___x_2061_, 1, v_k_2054_);
lean_ctor_set(v___x_2061_, 0, v___x_2122_);
v___x_2127_ = v___x_2061_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_r_2057_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
else
{
lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2189_; 
lean_inc(v_r_2057_);
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
lean_inc(v_size_2053_);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_r_2039_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; 
v_unused_2190_ = lean_ctor_get(v_r_2039_, 4);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_r_2039_, 3);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_r_2039_, 2);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_2039_, 1);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_2039_, 0);
lean_dec(v_unused_2194_);
v___x_2137_ = v_r_2039_;
v_isShared_2138_ = v_isSharedCheck_2189_;
goto v_resetjp_2136_;
}
else
{
lean_dec(v_r_2039_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2189_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
if (lean_obj_tag(v_l_2056_) == 0)
{
if (lean_obj_tag(v_r_2057_) == 0)
{
lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v_size_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_inc(v_tree_2064_);
v_k_2139_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_k_2139_);
v_v_2140_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_v_2140_);
lean_dec_ref(v___x_2063_);
v_size_2141_ = lean_ctor_get(v_l_2056_, 0);
v___x_2142_ = lean_nat_add(v___x_2058_, v_size_2053_);
lean_dec(v_size_2053_);
v___x_2143_ = lean_nat_add(v___x_2058_, v_size_2141_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 4, v_l_2056_);
lean_ctor_set(v___x_2137_, 3, v_tree_2064_);
lean_ctor_set(v___x_2137_, 2, v_v_2140_);
lean_ctor_set(v___x_2137_, 1, v_k_2139_);
lean_ctor_set(v___x_2137_, 0, v___x_2143_);
v___x_2145_ = v___x_2137_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_tree_2064_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_l_2056_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_r_2057_);
lean_ctor_set(v___x_2061_, 3, v___x_2145_);
lean_ctor_set(v___x_2061_, 2, v_v_2055_);
lean_ctor_set(v___x_2061_, 1, v_k_2054_);
lean_ctor_set(v___x_2061_, 0, v___x_2142_);
v___x_2147_ = v___x_2061_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_r_2057_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
lean_object* v_k_2150_; lean_object* v_v_2151_; lean_object* v_k_2152_; lean_object* v_v_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_size_2053_);
v_k_2150_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_k_2150_);
v_v_2151_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_v_2151_);
lean_dec_ref(v___x_2063_);
v_k_2152_ = lean_ctor_get(v_l_2056_, 1);
v_v_2153_ = lean_ctor_get(v_l_2056_, 2);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2168_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2170_);
v___x_2155_ = v_l_2056_;
v_isShared_2156_ = v_isSharedCheck_2167_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_v_2153_);
lean_inc(v_k_2152_);
lean_dec(v_l_2056_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2167_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_unsigned_to_nat(3u);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 4, v_r_2057_);
lean_ctor_set(v___x_2155_, 3, v_r_2057_);
lean_ctor_set(v___x_2155_, 2, v_v_2151_);
lean_ctor_set(v___x_2155_, 1, v_k_2150_);
lean_ctor_set(v___x_2155_, 0, v___x_2058_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_k_2150_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_v_2151_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v_r_2057_);
v___x_2159_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 3, v_r_2057_);
lean_ctor_set(v___x_2137_, 0, v___x_2058_);
v___x_2161_ = v___x_2137_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_r_2057_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2163_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v___x_2161_);
lean_ctor_set(v___x_2061_, 3, v___x_2159_);
lean_ctor_set(v___x_2061_, 2, v_v_2153_);
lean_ctor_set(v___x_2061_, 1, v_k_2152_);
lean_ctor_set(v___x_2061_, 0, v___x_2157_);
v___x_2163_ = v___x_2061_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2152_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2153_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2057_) == 0)
{
lean_object* v_k_2171_; lean_object* v_v_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
lean_dec(v_size_2053_);
v_k_2171_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_k_2171_);
v_v_2172_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_v_2172_);
lean_dec_ref(v___x_2063_);
v___x_2173_ = lean_unsigned_to_nat(3u);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 4, v_l_2056_);
lean_ctor_set(v___x_2137_, 2, v_v_2172_);
lean_ctor_set(v___x_2137_, 1, v_k_2171_);
lean_ctor_set(v___x_2137_, 0, v___x_2058_);
v___x_2175_ = v___x_2137_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_l_2056_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_r_2057_);
lean_ctor_set(v___x_2061_, 3, v___x_2175_);
lean_ctor_set(v___x_2061_, 2, v_v_2055_);
lean_ctor_set(v___x_2061_, 1, v_k_2054_);
lean_ctor_set(v___x_2061_, 0, v___x_2173_);
v___x_2177_ = v___x_2061_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_r_2057_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_k_2180_; lean_object* v_v_2181_; lean_object* v___x_2183_; 
v_k_2180_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_k_2180_);
v_v_2181_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_v_2181_);
lean_dec_ref(v___x_2063_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 3, v_r_2057_);
v___x_2183_ = v___x_2137_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_size_2053_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_r_2057_);
v___x_2183_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = lean_unsigned_to_nat(2u);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v___x_2183_);
lean_ctor_set(v___x_2061_, 3, v_r_2057_);
lean_ctor_set(v___x_2061_, 2, v_v_2181_);
lean_ctor_set(v___x_2061_, 1, v_k_2180_);
lean_ctor_set(v___x_2061_, 0, v___x_2184_);
v___x_2186_ = v___x_2061_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2180_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2181_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v___x_2183_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
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
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2353_; 
lean_inc(v_r_2057_);
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_r_2039_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; lean_object* v_unused_2355_; lean_object* v_unused_2356_; lean_object* v_unused_2357_; lean_object* v_unused_2358_; 
v_unused_2354_ = lean_ctor_get(v_r_2039_, 4);
lean_dec(v_unused_2354_);
v_unused_2355_ = lean_ctor_get(v_r_2039_, 3);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_r_2039_, 2);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_r_2039_, 1);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_r_2039_, 0);
lean_dec(v_unused_2358_);
v___x_2202_ = v_r_2039_;
v_isShared_2203_ = v_isSharedCheck_2353_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v_r_2039_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2353_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v_tree_2205_; 
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2054_, v_v_2055_, v_l_2056_, v_r_2057_);
v_tree_2205_ = lean_ctor_get(v___x_2204_, 2);
lean_inc(v_tree_2205_);
if (lean_obj_tag(v_tree_2205_) == 0)
{
lean_object* v_k_2206_; lean_object* v_v_2207_; lean_object* v_size_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_k_2206_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_k_2206_);
v_v_2207_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_v_2207_);
lean_dec_ref(v___x_2204_);
v_size_2208_ = lean_ctor_get(v_tree_2205_, 0);
v___x_2209_ = lean_unsigned_to_nat(3u);
v___x_2210_ = lean_nat_mul(v___x_2209_, v_size_2208_);
v___x_2211_ = lean_nat_dec_lt(v___x_2210_, v_size_2048_);
lean_dec(v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec(v_r_2052_);
v___x_2212_ = lean_nat_add(v___x_2058_, v_size_2048_);
v___x_2213_ = lean_nat_add(v___x_2212_, v_size_2208_);
lean_dec(v___x_2212_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_tree_2205_);
lean_ctor_set(v___x_2202_, 3, v_l_2038_);
lean_ctor_set(v___x_2202_, 2, v_v_2207_);
lean_ctor_set(v___x_2202_, 1, v_k_2206_);
lean_ctor_set(v___x_2202_, 0, v___x_2213_);
v___x_2215_ = v___x_2202_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_l_2038_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v_tree_2205_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2282_; 
lean_inc(v_l_2051_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
lean_inc(v_size_2048_);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_l_2038_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; lean_object* v_unused_2284_; lean_object* v_unused_2285_; lean_object* v_unused_2286_; lean_object* v_unused_2287_; 
v_unused_2283_ = lean_ctor_get(v_l_2038_, 4);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v_l_2038_, 3);
lean_dec(v_unused_2284_);
v_unused_2285_ = lean_ctor_get(v_l_2038_, 2);
lean_dec(v_unused_2285_);
v_unused_2286_ = lean_ctor_get(v_l_2038_, 1);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_l_2038_, 0);
lean_dec(v_unused_2287_);
v___x_2218_ = v_l_2038_;
v_isShared_2219_ = v_isSharedCheck_2282_;
goto v_resetjp_2217_;
}
else
{
lean_dec(v_l_2038_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2282_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_size_2220_; lean_object* v_size_2221_; lean_object* v_k_2222_; lean_object* v_v_2223_; lean_object* v_l_2224_; lean_object* v_r_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_size_2220_ = lean_ctor_get(v_l_2051_, 0);
v_size_2221_ = lean_ctor_get(v_r_2052_, 0);
v_k_2222_ = lean_ctor_get(v_r_2052_, 1);
v_v_2223_ = lean_ctor_get(v_r_2052_, 2);
v_l_2224_ = lean_ctor_get(v_r_2052_, 3);
v_r_2225_ = lean_ctor_get(v_r_2052_, 4);
v___x_2226_ = lean_unsigned_to_nat(2u);
v___x_2227_ = lean_nat_mul(v___x_2226_, v_size_2220_);
v___x_2228_ = lean_nat_dec_lt(v_size_2221_, v___x_2227_);
lean_dec(v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2266_; 
lean_inc(v_r_2225_);
lean_inc(v_l_2224_);
lean_inc(v_v_2223_);
lean_inc(v_k_2222_);
lean_del_object(v___x_2218_);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_r_2052_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; 
v_unused_2267_ = lean_ctor_get(v_r_2052_, 4);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_r_2052_, 3);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_r_2052_, 2);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_r_2052_, 1);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_r_2052_, 0);
lean_dec(v_unused_2271_);
v___x_2230_ = v_r_2052_;
v_isShared_2231_ = v_isSharedCheck_2266_;
goto v_resetjp_2229_;
}
else
{
lean_dec(v_r_2052_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2266_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___x_2254_; lean_object* v___y_2256_; 
v___x_2232_ = lean_nat_add(v___x_2058_, v_size_2048_);
lean_dec(v_size_2048_);
v___x_2233_ = lean_nat_add(v___x_2232_, v_size_2208_);
lean_dec(v___x_2232_);
v___x_2254_ = lean_nat_add(v___x_2058_, v_size_2220_);
if (lean_obj_tag(v_l_2224_) == 0)
{
lean_object* v_size_2264_; 
v_size_2264_ = lean_ctor_get(v_l_2224_, 0);
lean_inc(v_size_2264_);
v___y_2256_ = v_size_2264_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___y_2256_ = v___x_2265_;
goto v___jp_2255_;
}
v___jp_2234_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2238_ = lean_nat_add(v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec(v___y_2236_);
lean_inc_ref(v_tree_2205_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 4, v_tree_2205_);
lean_ctor_set(v___x_2230_, 3, v_r_2225_);
lean_ctor_set(v___x_2230_, 2, v_v_2207_);
lean_ctor_set(v___x_2230_, 1, v_k_2206_);
lean_ctor_set(v___x_2230_, 0, v___x_2238_);
v___x_2240_ = v___x_2230_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_r_2225_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_tree_2205_);
v___x_2240_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_isSharedCheck_2247_ = !lean_is_exclusive(v_tree_2205_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; lean_object* v_unused_2249_; lean_object* v_unused_2250_; lean_object* v_unused_2251_; lean_object* v_unused_2252_; 
v_unused_2248_ = lean_ctor_get(v_tree_2205_, 4);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_tree_2205_, 3);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_tree_2205_, 2);
lean_dec(v_unused_2250_);
v_unused_2251_ = lean_ctor_get(v_tree_2205_, 1);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_tree_2205_, 0);
lean_dec(v_unused_2252_);
v___x_2242_ = v_tree_2205_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_dec(v_tree_2205_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 4, v___x_2240_);
lean_ctor_set(v___x_2242_, 3, v___y_2235_);
lean_ctor_set(v___x_2242_, 2, v_v_2223_);
lean_ctor_set(v___x_2242_, 1, v_k_2222_);
lean_ctor_set(v___x_2242_, 0, v___x_2233_);
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_k_2222_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_v_2223_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v___y_2235_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v___x_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_nat_add(v___x_2254_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec(v___x_2254_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_l_2224_);
lean_ctor_set(v___x_2202_, 3, v_l_2051_);
lean_ctor_set(v___x_2202_, 2, v_v_2050_);
lean_ctor_set(v___x_2202_, 1, v_k_2049_);
lean_ctor_set(v___x_2202_, 0, v___x_2257_);
v___x_2259_ = v___x_2202_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_l_2224_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_nat_add(v___x_2058_, v_size_2208_);
if (lean_obj_tag(v_r_2225_) == 0)
{
lean_object* v_size_2261_; 
v_size_2261_ = lean_ctor_get(v_r_2225_, 0);
lean_inc(v_size_2261_);
v___y_2235_ = v___x_2259_;
v___y_2236_ = v___x_2260_;
v___y_2237_ = v_size_2261_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
v___y_2235_ = v___x_2259_;
v___y_2236_ = v___x_2260_;
v___y_2237_ = v___x_2262_;
goto v___jp_2234_;
}
}
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2272_ = lean_nat_add(v___x_2058_, v_size_2048_);
lean_dec(v_size_2048_);
v___x_2273_ = lean_nat_add(v___x_2272_, v_size_2208_);
lean_dec(v___x_2272_);
v___x_2274_ = lean_nat_add(v___x_2058_, v_size_2208_);
v___x_2275_ = lean_nat_add(v___x_2274_, v_size_2221_);
lean_dec(v___x_2274_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_tree_2205_);
lean_ctor_set(v___x_2202_, 3, v_r_2052_);
lean_ctor_set(v___x_2202_, 2, v_v_2207_);
lean_ctor_set(v___x_2202_, 1, v_k_2206_);
lean_ctor_set(v___x_2202_, 0, v___x_2275_);
v___x_2277_ = v___x_2202_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_r_2052_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_tree_2205_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 4, v___x_2277_);
lean_ctor_set(v___x_2218_, 0, v___x_2273_);
v___x_2279_ = v___x_2218_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2051_) == 0)
{
lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2311_; 
lean_inc_ref(v_l_2051_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
lean_inc(v_size_2048_);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_l_2038_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; lean_object* v_unused_2316_; 
v_unused_2312_ = lean_ctor_get(v_l_2038_, 4);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_l_2038_, 3);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_l_2038_, 2);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_l_2038_, 1);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_l_2038_, 0);
lean_dec(v_unused_2316_);
v___x_2289_ = v_l_2038_;
v_isShared_2290_ = v_isSharedCheck_2311_;
goto v_resetjp_2288_;
}
else
{
lean_dec(v_l_2038_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2311_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
if (lean_obj_tag(v_r_2052_) == 0)
{
lean_object* v_k_2291_; lean_object* v_v_2292_; lean_object* v_size_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v_k_2291_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_k_2291_);
v_v_2292_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_v_2292_);
lean_dec_ref(v___x_2204_);
v_size_2293_ = lean_ctor_get(v_r_2052_, 0);
v___x_2294_ = lean_nat_add(v___x_2058_, v_size_2048_);
lean_dec(v_size_2048_);
v___x_2295_ = lean_nat_add(v___x_2058_, v_size_2293_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_tree_2205_);
lean_ctor_set(v___x_2202_, 3, v_r_2052_);
lean_ctor_set(v___x_2202_, 2, v_v_2292_);
lean_ctor_set(v___x_2202_, 1, v_k_2291_);
lean_ctor_set(v___x_2202_, 0, v___x_2295_);
v___x_2297_ = v___x_2202_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2291_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2292_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v_r_2052_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v_tree_2205_);
v___x_2297_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2299_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 4, v___x_2297_);
lean_ctor_set(v___x_2289_, 0, v___x_2294_);
v___x_2299_ = v___x_2289_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_object* v_k_2302_; lean_object* v_v_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_dec(v_size_2048_);
v_k_2302_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_k_2302_);
v_v_2303_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_v_2303_);
lean_dec_ref(v___x_2204_);
v___x_2304_ = lean_unsigned_to_nat(3u);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_r_2052_);
lean_ctor_set(v___x_2202_, 3, v_r_2052_);
lean_ctor_set(v___x_2202_, 2, v_v_2303_);
lean_ctor_set(v___x_2202_, 1, v_k_2302_);
lean_ctor_set(v___x_2202_, 0, v___x_2058_);
v___x_2306_ = v___x_2202_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_k_2302_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_v_2303_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_r_2052_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v_r_2052_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 4, v___x_2306_);
lean_ctor_set(v___x_2289_, 0, v___x_2304_);
v___x_2308_ = v___x_2289_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2052_) == 0)
{
lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2341_; 
lean_inc(v_l_2051_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_l_2038_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; lean_object* v_unused_2346_; 
v_unused_2342_ = lean_ctor_get(v_l_2038_, 4);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_l_2038_, 3);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_l_2038_, 2);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_l_2038_, 1);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_l_2038_, 0);
lean_dec(v_unused_2346_);
v___x_2318_ = v_l_2038_;
v_isShared_2319_ = v_isSharedCheck_2341_;
goto v_resetjp_2317_;
}
else
{
lean_dec(v_l_2038_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2341_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_k_2320_; lean_object* v_v_2321_; lean_object* v_k_2322_; lean_object* v_v_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_k_2320_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_k_2320_);
v_v_2321_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_v_2321_);
lean_dec_ref(v___x_2204_);
v_k_2322_ = lean_ctor_get(v_r_2052_, 1);
v_v_2323_ = lean_ctor_get(v_r_2052_, 2);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_r_2052_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; lean_object* v_unused_2339_; lean_object* v_unused_2340_; 
v_unused_2338_ = lean_ctor_get(v_r_2052_, 4);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_2052_, 3);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_r_2052_, 0);
lean_dec(v_unused_2340_);
v___x_2325_ = v_r_2052_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_v_2323_);
lean_inc(v_k_2322_);
lean_dec(v_r_2052_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(3u);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v_l_2051_);
lean_ctor_set(v___x_2325_, 3, v_l_2051_);
lean_ctor_set(v___x_2325_, 2, v_v_2050_);
lean_ctor_set(v___x_2325_, 1, v_k_2049_);
lean_ctor_set(v___x_2325_, 0, v___x_2058_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_l_2051_);
v___x_2329_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_l_2051_);
lean_ctor_set(v___x_2202_, 3, v_l_2051_);
lean_ctor_set(v___x_2202_, 2, v_v_2321_);
lean_ctor_set(v___x_2202_, 1, v_k_2320_);
lean_ctor_set(v___x_2202_, 0, v___x_2058_);
v___x_2331_ = v___x_2202_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2320_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2321_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_l_2051_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 4, v___x_2331_);
lean_ctor_set(v___x_2318_, 3, v___x_2329_);
lean_ctor_set(v___x_2318_, 2, v_v_2323_);
lean_ctor_set(v___x_2318_, 1, v_k_2322_);
lean_ctor_set(v___x_2318_, 0, v___x_2327_);
v___x_2333_ = v___x_2318_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v___x_2331_);
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
else
{
lean_object* v_k_2347_; lean_object* v_v_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v_k_2347_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_k_2347_);
v_v_2348_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_v_2348_);
lean_dec_ref(v___x_2204_);
v___x_2349_ = lean_unsigned_to_nat(2u);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v_r_2052_);
lean_ctor_set(v___x_2202_, 3, v_l_2038_);
lean_ctor_set(v___x_2202_, 2, v_v_2348_);
lean_ctor_set(v___x_2202_, 1, v_k_2347_);
lean_ctor_set(v___x_2202_, 0, v___x_2349_);
v___x_2351_ = v___x_2202_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_k_2347_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_v_2348_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_l_2038_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v_r_2052_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
}
else
{
return v_l_2038_;
}
}
else
{
return v_r_2039_;
}
}
else
{
lean_object* v_val_2359_; lean_object* v___x_2361_; 
v_val_2359_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_val_2359_);
lean_dec_ref_known(v___x_2047_, 1);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 2, v_val_2359_);
lean_ctor_set(v___x_2041_, 1, v_k_2033_);
v___x_2361_ = v___x_2041_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_size_2035_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_k_2033_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_val_2359_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_l_2038_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v_r_2039_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
default: 
{
lean_object* v_impl_2363_; lean_object* v___x_2364_; 
lean_del_object(v___x_2041_);
lean_dec(v_size_2035_);
v_impl_2363_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2032_, v_k_2033_, v_r_2039_);
v___x_2364_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2036_, v_v_2037_, v_l_2038_, v_impl_2363_);
return v___x_2364_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2032_, v___x_2366_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec(v_k_2033_);
return v_t_2034_;
}
else
{
lean_object* v_val_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_val_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_val_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v_k_2033_);
lean_ctor_set(v___x_2370_, 2, v_val_2368_);
lean_ctor_set(v___x_2370_, 3, v_t_2034_);
lean_ctor_set(v___x_2370_, 4, v_t_2034_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2371_, lean_object* v_i_2372_, lean_object* v_k_2373_){
_start:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_array_get_size(v_keys_2371_);
v___x_2375_ = lean_nat_dec_lt(v_i_2372_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_dec(v_i_2372_);
return v___x_2375_;
}
else
{
lean_object* v_k_x27_2376_; uint8_t v___x_2377_; 
v_k_x27_2376_ = lean_array_fget_borrowed(v_keys_2371_, v_i_2372_);
v___x_2377_ = lean_name_eq(v_k_2373_, v_k_x27_2376_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = lean_nat_add(v_i_2372_, v___x_2378_);
lean_dec(v_i_2372_);
v_i_2372_ = v___x_2379_;
goto _start;
}
else
{
lean_dec(v_i_2372_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2381_, lean_object* v_i_2382_, lean_object* v_k_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2381_, v_i_2382_, v_k_2383_);
lean_dec(v_k_2383_);
lean_dec_ref(v_keys_2381_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_2386_, size_t v_x_2387_, lean_object* v_x_2388_){
_start:
{
if (lean_obj_tag(v_x_2386_) == 0)
{
lean_object* v_es_2389_; lean_object* v___x_2390_; size_t v___x_2391_; size_t v___x_2392_; lean_object* v_j_2393_; lean_object* v___x_2394_; 
v_es_2389_ = lean_ctor_get(v_x_2386_, 0);
v___x_2390_ = lean_box(2);
v___x_2391_ = ((size_t)31ULL);
v___x_2392_ = lean_usize_land(v_x_2387_, v___x_2391_);
v_j_2393_ = lean_usize_to_nat(v___x_2392_);
v___x_2394_ = lean_array_get_borrowed(v___x_2390_, v_es_2389_, v_j_2393_);
lean_dec(v_j_2393_);
switch(lean_obj_tag(v___x_2394_))
{
case 0:
{
lean_object* v_key_2395_; uint8_t v___x_2396_; 
v_key_2395_ = lean_ctor_get(v___x_2394_, 0);
v___x_2396_ = lean_name_eq(v_x_2388_, v_key_2395_);
return v___x_2396_;
}
case 1:
{
lean_object* v_node_2397_; size_t v___x_2398_; size_t v___x_2399_; 
v_node_2397_ = lean_ctor_get(v___x_2394_, 0);
v___x_2398_ = ((size_t)5ULL);
v___x_2399_ = lean_usize_shift_right(v_x_2387_, v___x_2398_);
v_x_2386_ = v_node_2397_;
v_x_2387_ = v___x_2399_;
goto _start;
}
default: 
{
uint8_t v___x_2401_; 
v___x_2401_ = 0;
return v___x_2401_;
}
}
}
else
{
lean_object* v_ks_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_ks_2402_ = lean_ctor_get(v_x_2386_, 0);
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_2402_, v___x_2403_, v_x_2388_);
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
size_t v_x_3827__boxed_2408_; uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_x_3827__boxed_2408_ = lean_unbox_usize(v_x_2406_);
lean_dec(v_x_2406_);
v_res_2409_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2405_, v_x_3827__boxed_2408_, v_x_2407_);
lean_dec(v_x_2407_);
lean_dec_ref(v_x_2405_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint64_t v___y_2414_; 
if (lean_obj_tag(v_x_2412_) == 0)
{
uint64_t v___x_2417_; 
v___x_2417_ = 1723ULL;
v___y_2414_ = v___x_2417_;
goto v___jp_2413_;
}
else
{
uint64_t v_hash_2418_; 
v_hash_2418_ = lean_ctor_get_uint64(v_x_2412_, sizeof(void*)*2);
v___y_2414_ = v_hash_2418_;
goto v___jp_2413_;
}
v___jp_2413_:
{
size_t v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = lean_uint64_to_usize(v___y_2414_);
v___x_2416_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2411_, v___x_2415_, v_x_2412_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_2419_, lean_object* v_x_2420_){
_start:
{
uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_res_2421_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2419_, v_x_2420_);
lean_dec(v_x_2420_);
lean_dec_ref(v_x_2419_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_2423_, lean_object* v_a_2424_, uint8_t v___x_2425_, lean_object* v_x_2426_, lean_object* v_____s_2427_){
_start:
{
lean_object* v_fst_2428_; lean_object* v_kinds_2429_; uint8_t v___x_2430_; 
v_fst_2428_ = lean_ctor_get(v_x_2426_, 0);
lean_inc(v_fst_2428_);
lean_dec_ref(v_x_2426_);
v_kinds_2429_ = lean_ctor_get(v_tactics_2423_, 1);
v___x_2430_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_2429_, v_fst_2428_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_dec(v_fst_2428_);
lean_dec(v_a_2424_);
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_____s_2427_);
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = l_Lean_Name_toString(v_a_2424_, v___x_2425_);
v___x_2433_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2432_, v_fst_2428_, v_____s_2427_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_2435_, lean_object* v_a_2436_, lean_object* v___x_2437_, lean_object* v_x_2438_, lean_object* v_____s_2439_){
_start:
{
uint8_t v___x_3883__boxed_2440_; lean_object* v_res_2441_; 
v___x_3883__boxed_2440_ = lean_unbox(v___x_2437_);
v_res_2441_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2435_, v_a_2436_, v___x_3883__boxed_2440_, v_x_2438_, v_____s_2439_);
lean_dec_ref(v_tactics_2435_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_2442_, lean_object* v_keys_2443_, lean_object* v_vals_2444_, lean_object* v_i_2445_, lean_object* v_acc_2446_){
_start:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = lean_array_get_size(v_keys_2443_);
v___x_2448_ = lean_nat_dec_lt(v_i_2445_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; 
lean_dec(v_i_2445_);
lean_dec_ref(v_f_2442_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_acc_2446_);
return v___x_2449_;
}
else
{
lean_object* v_k_2450_; lean_object* v_v_2451_; lean_object* v___x_2452_; 
v_k_2450_ = lean_array_fget_borrowed(v_keys_2443_, v_i_2445_);
v_v_2451_ = lean_array_fget_borrowed(v_vals_2444_, v_i_2445_);
lean_inc_ref(v_f_2442_);
lean_inc(v_v_2451_);
lean_inc(v_k_2450_);
v___x_2452_ = lean_apply_3(v_f_2442_, v_acc_2446_, v_k_2450_, v_v_2451_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_dec(v_i_2445_);
lean_dec_ref(v_f_2442_);
return v___x_2452_;
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_nat_add(v_i_2445_, v___x_2454_);
lean_dec(v_i_2445_);
v_i_2445_ = v___x_2455_;
v_acc_2446_ = v_a_2453_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_2457_, lean_object* v_keys_2458_, lean_object* v_vals_2459_, lean_object* v_i_2460_, lean_object* v_acc_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2457_, v_keys_2458_, v_vals_2459_, v_i_2460_, v_acc_2461_);
lean_dec_ref(v_vals_2459_);
lean_dec_ref(v_keys_2458_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_2463_, lean_object* v_as_2464_, size_t v_i_2465_, size_t v_stop_2466_, lean_object* v_b_2467_){
_start:
{
lean_object* v_a_2469_; lean_object* v___y_2474_; uint8_t v___x_2476_; 
v___x_2476_ = lean_usize_dec_eq(v_i_2465_, v_stop_2466_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_array_uget_borrowed(v_as_2464_, v_i_2465_);
switch(lean_obj_tag(v___x_2477_))
{
case 0:
{
lean_object* v_key_2478_; lean_object* v_val_2479_; lean_object* v___x_2480_; 
v_key_2478_ = lean_ctor_get(v___x_2477_, 0);
v_val_2479_ = lean_ctor_get(v___x_2477_, 1);
lean_inc_ref(v_f_2463_);
lean_inc(v_val_2479_);
lean_inc(v_key_2478_);
v___x_2480_ = lean_apply_3(v_f_2463_, v_b_2467_, v_key_2478_, v_val_2479_);
v___y_2474_ = v___x_2480_;
goto v___jp_2473_;
}
case 1:
{
lean_object* v_node_2481_; lean_object* v___x_2482_; 
v_node_2481_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_node_2481_);
lean_inc_ref(v_f_2463_);
v___x_2482_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2463_, v_node_2481_, v_b_2467_);
v___y_2474_ = v___x_2482_;
goto v___jp_2473_;
}
default: 
{
v_a_2469_ = v_b_2467_;
goto v___jp_2468_;
}
}
}
else
{
lean_object* v___x_2483_; 
lean_dec_ref(v_f_2463_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_b_2467_);
return v___x_2483_;
}
v___jp_2468_:
{
size_t v___x_2470_; size_t v___x_2471_; 
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2465_, v___x_2470_);
v_i_2465_ = v___x_2471_;
v_b_2467_ = v_a_2469_;
goto _start;
}
v___jp_2473_:
{
if (lean_obj_tag(v___y_2474_) == 0)
{
lean_dec_ref(v_f_2463_);
return v___y_2474_;
}
else
{
lean_object* v_a_2475_; 
v_a_2475_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___y_2474_, 1);
v_a_2469_ = v_a_2475_;
goto v___jp_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
if (lean_obj_tag(v_x_2485_) == 0)
{
lean_object* v_es_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2500_; 
v_es_2487_ = lean_ctor_get(v_x_2485_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_x_2485_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2489_ = v_x_2485_;
v_isShared_2490_ = v_isSharedCheck_2500_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_es_2487_);
lean_dec(v_x_2485_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2500_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_array_get_size(v_es_2487_);
v___x_2493_ = lean_nat_dec_lt(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2495_; 
lean_dec_ref(v_es_2487_);
lean_dec_ref(v_f_2484_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 1);
lean_ctor_set(v___x_2489_, 0, v_x_2486_);
v___x_2495_ = v___x_2489_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_x_2486_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
else
{
size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
lean_del_object(v___x_2489_);
v___x_2497_ = ((size_t)0ULL);
v___x_2498_ = lean_usize_of_nat(v___x_2492_);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2484_, v_es_2487_, v___x_2497_, v___x_2498_, v_x_2486_);
lean_dec_ref(v_es_2487_);
return v___x_2499_;
}
}
}
else
{
lean_object* v_ks_2501_; lean_object* v_vs_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_ks_2501_ = lean_ctor_get(v_x_2485_, 0);
lean_inc_ref(v_ks_2501_);
v_vs_2502_ = lean_ctor_get(v_x_2485_, 1);
lean_inc_ref(v_vs_2502_);
lean_dec_ref_known(v_x_2485_, 2);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2484_, v_ks_2501_, v_vs_2502_, v___x_2503_, v_x_2486_);
lean_dec_ref(v_vs_2502_);
lean_dec_ref(v_ks_2501_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_stop_2508_, lean_object* v_b_2509_){
_start:
{
size_t v_i_boxed_2510_; size_t v_stop_boxed_2511_; lean_object* v_res_2512_; 
v_i_boxed_2510_ = lean_unbox_usize(v_i_2507_);
lean_dec(v_i_2507_);
v_stop_boxed_2511_ = lean_unbox_usize(v_stop_2508_);
lean_dec(v_stop_2508_);
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2505_, v_as_2506_, v_i_boxed_2510_, v_stop_boxed_2511_, v_b_2509_);
lean_dec_ref(v_as_2506_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_2513_, lean_object* v_s_2514_, lean_object* v_a_2515_, lean_object* v_b_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2515_);
lean_ctor_set(v___x_2517_, 1, v_b_2516_);
v___x_2518_ = lean_apply_2(v_f_2513_, v___x_2517_, v_s_2514_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_a_2527_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2518_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2518_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_2535_, lean_object* v_init_2536_, lean_object* v_f_2537_){
_start:
{
lean_object* v___f_2538_; lean_object* v___x_2539_; lean_object* v_a_2540_; 
v___f_2538_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2538_, 0, v_f_2537_);
lean_inc_ref(v_map_2535_);
v___x_2539_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_2538_, v_map_2535_, v_init_2536_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2539_);
return v_a_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_2541_, lean_object* v_init_2542_, lean_object* v_f_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2541_, v_init_2542_, v_f_2543_);
lean_dec_ref(v_map_2541_);
return v_res_2544_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_2547_, lean_object* v_a_2548_, uint8_t v___x_2549_, lean_object* v_as_x27_2550_, lean_object* v_b_2551_){
_start:
{
if (lean_obj_tag(v_as_x27_2550_) == 0)
{
lean_dec(v_a_2548_);
lean_dec_ref(v_tactics_2547_);
return v_b_2551_;
}
else
{
lean_object* v_head_2552_; lean_object* v_fst_2553_; lean_object* v_info_2554_; lean_object* v_tail_2555_; lean_object* v_collectKinds_2556_; lean_object* v___x_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_head_2552_ = lean_ctor_get(v_as_x27_2550_, 0);
v_fst_2553_ = lean_ctor_get(v_head_2552_, 0);
v_info_2554_ = lean_ctor_get(v_fst_2553_, 0);
v_tail_2555_ = lean_ctor_get(v_as_x27_2550_, 1);
v_collectKinds_2556_ = lean_ctor_get(v_info_2554_, 1);
v___x_2557_ = lean_box(v___x_2549_);
lean_inc(v_a_2548_);
lean_inc_ref(v_tactics_2547_);
v___f_2558_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2558_, 0, v_tactics_2547_);
lean_closure_set(v___f_2558_, 1, v_a_2548_);
lean_closure_set(v___f_2558_, 2, v___x_2557_);
v___x_2559_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_2556_);
v___x_2560_ = lean_apply_1(v_collectKinds_2556_, v___x_2559_);
v___x_2561_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_2560_, v_b_2551_, v___f_2558_);
lean_dec_ref(v___x_2560_);
v_as_x27_2550_ = v_tail_2555_;
v_b_2551_ = v___x_2561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_2563_, lean_object* v_a_2564_, lean_object* v___x_2565_, lean_object* v_as_x27_2566_, lean_object* v_b_2567_){
_start:
{
uint8_t v___x_4042__boxed_2568_; lean_object* v_res_2569_; 
v___x_4042__boxed_2568_ = lean_unbox(v___x_2565_);
v_res_2569_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2563_, v_a_2564_, v___x_4042__boxed_2568_, v_as_x27_2566_, v_b_2567_);
lean_dec(v_as_x27_2566_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_2572_, lean_object* v_init_2573_, lean_object* v_x_2574_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v_k_2575_; lean_object* v_v_2576_; lean_object* v_l_2577_; lean_object* v_r_2578_; lean_object* v___x_2579_; lean_object* v_a_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_k_2575_ = lean_ctor_get(v_x_2574_, 1);
lean_inc(v_k_2575_);
v_v_2576_ = lean_ctor_get(v_x_2574_, 2);
lean_inc(v_v_2576_);
v_l_2577_ = lean_ctor_get(v_x_2574_, 3);
lean_inc(v_l_2577_);
v_r_2578_ = lean_ctor_get(v_x_2574_, 4);
lean_inc(v_r_2578_);
lean_dec_ref_known(v_x_2574_, 5);
lean_inc_ref(v_tactics_2572_);
v___x_2579_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2572_, v_init_2573_, v_l_2577_);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v___x_2581_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0));
v___x_2582_ = lean_name_eq(v_k_2575_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
lean_inc(v_a_2580_);
lean_dec_ref(v___x_2579_);
lean_inc_ref(v_tactics_2572_);
v___x_2583_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2572_, v_k_2575_, v___x_2582_, v_v_2576_, v_a_2580_);
lean_dec(v_v_2576_);
v_init_2573_ = v___x_2583_;
v_x_2574_ = v_r_2578_;
goto _start;
}
else
{
lean_object* v_a_2585_; 
lean_dec(v_v_2576_);
lean_dec(v_k_2575_);
v_a_2585_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___x_2579_);
v_init_2573_ = v_a_2585_;
v_x_2574_ = v_r_2578_;
goto _start;
}
}
else
{
lean_object* v___x_2587_; 
lean_dec_ref(v_tactics_2572_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_init_2573_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_2588_, lean_object* v_table_2589_, lean_object* v_firsts_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v_a_2592_; 
v___x_2591_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2588_, v_firsts_2590_, v_table_2589_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
return v_a_2592_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2594_, v_x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_2597_, lean_object* v_x_2598_, lean_object* v_x_2599_){
_start:
{
uint8_t v_res_2600_; lean_object* v_r_2601_; 
v_res_2600_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_2597_, v_x_2598_, v_x_2599_);
lean_dec(v_x_2599_);
lean_dec_ref(v_x_2598_);
v_r_2601_ = lean_box(v_res_2600_);
return v_r_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_2602_, lean_object* v_k_2603_, lean_object* v_t_2604_, lean_object* v_hl_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2602_, v_k_2603_, v_t_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_2607_, lean_object* v_00_u03b2_2608_, lean_object* v_map_2609_, lean_object* v_init_2610_, lean_object* v_f_2611_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2609_, v_init_2610_, v_f_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_2613_, lean_object* v_00_u03b2_2614_, lean_object* v_map_2615_, lean_object* v_init_2616_, lean_object* v_f_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_2613_, v_00_u03b2_2614_, v_map_2615_, v_init_2616_, v_f_2617_);
lean_dec_ref(v_map_2615_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_2619_, lean_object* v_a_2620_, uint8_t v___x_2621_, lean_object* v_as_2622_, lean_object* v_as_x27_2623_, lean_object* v_b_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2619_, v_a_2620_, v___x_2621_, v_as_x27_2623_, v_b_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_2627_, lean_object* v_a_2628_, lean_object* v___x_2629_, lean_object* v_as_2630_, lean_object* v_as_x27_2631_, lean_object* v_b_2632_, lean_object* v_a_2633_){
_start:
{
uint8_t v___x_4122__boxed_2634_; lean_object* v_res_2635_; 
v___x_4122__boxed_2634_ = lean_unbox(v___x_2629_);
v_res_2635_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2627_, v_a_2628_, v___x_4122__boxed_2634_, v_as_2630_, v_as_x27_2631_, v_b_2632_, v_a_2633_);
lean_dec(v_as_x27_2631_);
lean_dec(v_as_2630_);
return v_res_2635_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_2636_, lean_object* v_x_2637_, size_t v_x_2638_, lean_object* v_x_2639_){
_start:
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2637_, v_x_2638_, v_x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
size_t v_x_4131__boxed_2645_; uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_x_4131__boxed_2645_ = lean_unbox_usize(v_x_2643_);
lean_dec(v_x_2643_);
v_res_2646_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_2641_, v_x_2642_, v_x_4131__boxed_2645_, v_x_2644_);
lean_dec(v_x_2644_);
lean_dec_ref(v_x_2642_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_2648_, lean_object* v_f_2649_, lean_object* v_init_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2649_, v_map_2648_, v_init_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_2652_, lean_object* v_00_u03c3_2653_, lean_object* v_00_u03b2_2654_, lean_object* v_map_2655_, lean_object* v_f_2656_, lean_object* v_init_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2656_, v_map_2655_, v_init_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2659_, lean_object* v_keys_2660_, lean_object* v_vals_2661_, lean_object* v_heq_2662_, lean_object* v_i_2663_, lean_object* v_k_2664_){
_start:
{
uint8_t v___x_2665_; 
v___x_2665_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2660_, v_i_2663_, v_k_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2666_, lean_object* v_keys_2667_, lean_object* v_vals_2668_, lean_object* v_heq_2669_, lean_object* v_i_2670_, lean_object* v_k_2671_){
_start:
{
uint8_t v_res_2672_; lean_object* v_r_2673_; 
v_res_2672_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_2666_, v_keys_2667_, v_vals_2668_, v_heq_2669_, v_i_2670_, v_k_2671_);
lean_dec(v_k_2671_);
lean_dec_ref(v_vals_2668_);
lean_dec_ref(v_keys_2667_);
v_r_2673_ = lean_box(v_res_2672_);
return v_r_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_2674_, lean_object* v_00_u03c3_2675_, lean_object* v_00_u03b1_2676_, lean_object* v_00_u03b2_2677_, lean_object* v_f_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2678_, v_x_2679_, v_x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_2682_, lean_object* v_00_u03b2_2683_, lean_object* v_00_u03c3_2684_, lean_object* v_00_u03c3_2685_, lean_object* v_f_2686_, lean_object* v_as_2687_, size_t v_i_2688_, size_t v_stop_2689_, lean_object* v_b_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2686_, v_as_2687_, v_i_2688_, v_stop_2689_, v_b_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_00_u03b2_2693_, lean_object* v_00_u03c3_2694_, lean_object* v_00_u03c3_2695_, lean_object* v_f_2696_, lean_object* v_as_2697_, lean_object* v_i_2698_, lean_object* v_stop_2699_, lean_object* v_b_2700_){
_start:
{
size_t v_i_boxed_2701_; size_t v_stop_boxed_2702_; lean_object* v_res_2703_; 
v_i_boxed_2701_ = lean_unbox_usize(v_i_2698_);
lean_dec(v_i_2698_);
v_stop_boxed_2702_ = lean_unbox_usize(v_stop_2699_);
lean_dec(v_stop_2699_);
v_res_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_2692_, v_00_u03b2_2693_, v_00_u03c3_2694_, v_00_u03c3_2695_, v_f_2696_, v_as_2697_, v_i_boxed_2701_, v_stop_boxed_2702_, v_b_2700_);
lean_dec_ref(v_as_2697_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_2704_, lean_object* v_00_u03c3_2705_, lean_object* v_00_u03b1_2706_, lean_object* v_00_u03b2_2707_, lean_object* v_f_2708_, lean_object* v_keys_2709_, lean_object* v_vals_2710_, lean_object* v_heq_2711_, lean_object* v_i_2712_, lean_object* v_acc_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2708_, v_keys_2709_, v_vals_2710_, v_i_2712_, v_acc_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_2715_, lean_object* v_00_u03c3_2716_, lean_object* v_00_u03b1_2717_, lean_object* v_00_u03b2_2718_, lean_object* v_f_2719_, lean_object* v_keys_2720_, lean_object* v_vals_2721_, lean_object* v_heq_2722_, lean_object* v_i_2723_, lean_object* v_acc_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_2715_, v_00_u03c3_2716_, v_00_u03b1_2717_, v_00_u03b2_2718_, v_f_2719_, v_keys_2720_, v_vals_2721_, v_heq_2722_, v_i_2723_, v_acc_2724_);
lean_dec_ref(v_vals_2721_);
lean_dec_ref(v_keys_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_2726_, lean_object* v_x2_2727_){
_start:
{
lean_object* v_fst_2728_; lean_object* v_snd_2729_; lean_object* v___x_2730_; 
v_fst_2728_ = lean_ctor_get(v_x2_2727_, 0);
lean_inc(v_fst_2728_);
v_snd_2729_ = lean_ctor_get(v_x2_2727_, 1);
lean_inc(v_snd_2729_);
lean_dec_ref(v_x2_2727_);
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2728_, v_snd_2729_, v_x1_2726_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_2750_, lean_object* v_x1_2751_, lean_object* v_x2_2752_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = lean_array_get_size(v_x2_2752_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2756_ = lean_nat_dec_lt(v___x_2753_, v___x_2754_);
if (v___x_2756_ == 0)
{
lean_dec_ref(v_x2_2752_);
lean_dec_ref(v___f_2750_);
return v_x1_2751_;
}
else
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_nat_dec_le(v___x_2754_, v___x_2754_);
if (v___x_2757_ == 0)
{
if (v___x_2756_ == 0)
{
lean_dec_ref(v_x2_2752_);
lean_dec_ref(v___f_2750_);
return v_x1_2751_;
}
else
{
size_t v___x_2758_; size_t v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = lean_usize_of_nat(v___x_2754_);
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2755_, v___f_2750_, v_x2_2752_, v___x_2758_, v___x_2759_, v_x1_2751_);
return v___x_2760_;
}
}
else
{
size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = ((size_t)0ULL);
v___x_2762_ = lean_usize_of_nat(v___x_2754_);
v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2755_, v___f_2750_, v_x2_2752_, v___x_2761_, v___x_2762_, v_x1_2751_);
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, lean_object* v___x_2771_, lean_object* v_toPure_2772_, lean_object* v___f_2773_, lean_object* v_env_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v_ext_2776_; lean_object* v_toEnvExtension_2777_; lean_object* v_asyncMode_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v_categories_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2775_ = l_Lean_Parser_parserExtension;
v_ext_2776_ = lean_ctor_get(v___x_2775_, 1);
v_toEnvExtension_2777_ = lean_ctor_get(v_ext_2776_, 0);
v_asyncMode_2778_ = lean_ctor_get(v_toEnvExtension_2777_, 2);
v___x_2779_ = 0;
lean_inc_ref(v_env_2774_);
v___x_2780_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2767_, v___x_2775_, v_env_2774_, v_asyncMode_2778_, v___x_2779_);
v_categories_2781_ = lean_ctor_get(v___x_2780_, 2);
lean_inc_ref(v_categories_2781_);
lean_dec(v___x_2780_);
v___x_2782_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2783_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2768_, v___x_2769_, v_categories_2781_, v___x_2782_);
lean_dec_ref(v_categories_2781_);
if (lean_obj_tag(v___x_2783_) == 1)
{
lean_object* v_val_2784_; lean_object* v___y_2786_; lean_object* v___x_2793_; lean_object* v_toEnvExtension_2794_; lean_object* v_exportEntriesFn_2795_; lean_object* v_asyncMode_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_importedEntries_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_exported_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v_val_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_val_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2793_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2794_ = lean_ctor_get(v___x_2793_, 0);
v_exportEntriesFn_2795_ = lean_ctor_get(v___x_2793_, 4);
v_asyncMode_2796_ = lean_ctor_get(v_toEnvExtension_2794_, 2);
v___x_2797_ = lean_box(0);
lean_inc_ref_n(v_env_2774_, 2);
v___x_2798_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2770_, v_toEnvExtension_2794_, v_env_2774_, v_asyncMode_2796_, v___x_2797_, v___x_2779_);
v_importedEntries_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc_ref(v_importedEntries_2799_);
lean_dec(v___x_2798_);
v___x_2800_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2771_, v___x_2793_, v_env_2774_, v_asyncMode_2796_, v___x_2797_, v___x_2779_);
lean_inc_ref(v_exportEntriesFn_2795_);
v___x_2801_ = lean_apply_2(v_exportEntriesFn_2795_, v_env_2774_, v___x_2800_);
v_exported_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_exported_2802_);
lean_dec_ref(v___x_2801_);
v___x_2803_ = lean_box(1);
v___x_2804_ = lean_array_push(v_importedEntries_2799_, v_exported_2802_);
v___x_2805_ = lean_unsigned_to_nat(0u);
v___x_2806_ = lean_array_get_size(v___x_2804_);
v___x_2807_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2808_ = lean_nat_dec_lt(v___x_2805_, v___x_2806_);
if (v___x_2808_ == 0)
{
lean_dec_ref(v___x_2804_);
lean_dec_ref(v___f_2773_);
v___y_2786_ = v___x_2803_;
goto v___jp_2785_;
}
else
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_nat_dec_le(v___x_2806_, v___x_2806_);
if (v___x_2809_ == 0)
{
if (v___x_2808_ == 0)
{
lean_dec_ref(v___x_2804_);
lean_dec_ref(v___f_2773_);
v___y_2786_ = v___x_2803_;
goto v___jp_2785_;
}
else
{
size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = ((size_t)0ULL);
v___x_2811_ = lean_usize_of_nat(v___x_2806_);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2807_, v___f_2773_, v___x_2804_, v___x_2810_, v___x_2811_, v___x_2803_);
v___y_2786_ = v___x_2812_;
goto v___jp_2785_;
}
}
else
{
size_t v___x_2813_; size_t v___x_2814_; lean_object* v___x_2815_; 
v___x_2813_ = ((size_t)0ULL);
v___x_2814_ = lean_usize_of_nat(v___x_2806_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2807_, v___f_2773_, v___x_2804_, v___x_2813_, v___x_2814_, v___x_2803_);
v___y_2786_ = v___x_2815_;
goto v___jp_2785_;
}
}
v___jp_2785_:
{
lean_object* v_tables_2787_; lean_object* v_leadingTable_2788_; lean_object* v_trailingTable_2789_; lean_object* v_firstTokens_2790_; lean_object* v_firstTokens_2791_; lean_object* v___x_2792_; 
v_tables_2787_ = lean_ctor_get(v_val_2784_, 2);
v_leadingTable_2788_ = lean_ctor_get(v_tables_2787_, 0);
v_trailingTable_2789_ = lean_ctor_get(v_tables_2787_, 2);
lean_inc(v_trailingTable_2789_);
lean_inc(v_leadingTable_2788_);
lean_inc(v_val_2784_);
v_firstTokens_2790_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2784_, v_leadingTable_2788_, v___y_2786_);
v_firstTokens_2791_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2784_, v_trailingTable_2789_, v_firstTokens_2790_);
v___x_2792_ = lean_apply_2(v_toPure_2772_, lean_box(0), v_firstTokens_2791_);
return v___x_2792_;
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec(v___x_2783_);
lean_dec_ref(v_env_2774_);
lean_dec_ref(v___f_2773_);
lean_dec(v___x_2771_);
v___x_2816_ = lean_box(1);
v___x_2817_ = lean_apply_2(v_toPure_2772_, lean_box(0), v___x_2816_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v_toPure_2823_, lean_object* v___f_2824_, lean_object* v_env_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_2818_, v___x_2819_, v___x_2820_, v___x_2821_, v___x_2822_, v_toPure_2823_, v___f_2824_, v_env_2825_);
lean_dec_ref(v___x_2821_);
lean_dec_ref(v___x_2818_);
return v_res_2826_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_box(1);
v___x_2831_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_2834_, lean_object* v_inst_2835_){
_start:
{
lean_object* v_toApplicative_2836_; lean_object* v_toBind_2837_; lean_object* v_getEnv_2838_; lean_object* v_toPure_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___f_2846_; lean_object* v___x_2847_; 
v_toApplicative_2836_ = lean_ctor_get(v_inst_2834_, 0);
lean_inc_ref(v_toApplicative_2836_);
v_toBind_2837_ = lean_ctor_get(v_inst_2834_, 1);
lean_inc(v_toBind_2837_);
lean_dec_ref(v_inst_2834_);
v_getEnv_2838_ = lean_ctor_get(v_inst_2835_, 0);
lean_inc(v_getEnv_2838_);
lean_dec_ref(v_inst_2835_);
v_toPure_2839_ = lean_ctor_get(v_toApplicative_2836_, 1);
lean_inc(v_toPure_2839_);
lean_dec_ref(v_toApplicative_2836_);
v___f_2840_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_2841_ = lean_box(1);
v___x_2842_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2843_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2844_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_2845_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_2846_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2846_, 0, v___x_2845_);
lean_closure_set(v___f_2846_, 1, v___x_2843_);
lean_closure_set(v___f_2846_, 2, v___x_2844_);
lean_closure_set(v___f_2846_, 3, v___x_2842_);
lean_closure_set(v___f_2846_, 4, v___x_2841_);
lean_closure_set(v___f_2846_, 5, v_toPure_2839_);
lean_closure_set(v___f_2846_, 6, v___f_2840_);
v___x_2847_ = lean_apply_4(v_toBind_2837_, lean_box(0), lean_box(0), v_getEnv_2838_, v___f_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_2849_, v_inst_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_box(1);
v___x_2855_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_2856_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2855_);
lean_ctor_set(v___x_2857_, 2, v___x_2854_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_2859_, lean_object* v___y_2860_, lean_object* v_toPure_2861_, lean_object* v_firsts_2862_, lean_object* v_____do__lift_2863_){
_start:
{
lean_object* v___y_2865_; lean_object* v_val_2876_; 
if (lean_obj_tag(v_____do__lift_2863_) == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_2859_);
v___x_2879_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_2878_, v_firsts_2862_, v_n_2859_);
if (lean_obj_tag(v___x_2879_) == 0)
{
uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = 1;
lean_inc(v_n_2859_);
v___x_2881_ = l_Lean_Name_toString(v_n_2859_, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
v___y_2865_ = v___x_2882_;
goto v___jp_2864_;
}
else
{
lean_object* v_val_2883_; 
v_val_2883_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_val_2883_);
lean_dec_ref_known(v___x_2879_, 1);
v_val_2876_ = v_val_2883_;
goto v___jp_2875_;
}
}
else
{
lean_object* v_val_2884_; 
lean_dec(v_firsts_2862_);
v_val_2884_ = lean_ctor_get(v_____do__lift_2863_, 0);
lean_inc(v_val_2884_);
lean_dec_ref_known(v_____do__lift_2863_, 1);
v_val_2876_ = v_val_2884_;
goto v___jp_2875_;
}
v___jp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2866_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_2867_ = l_Lean_Expr_const___override(v_n_2859_, v___y_2860_);
v___x_2868_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_2869_ = lean_box(0);
v___x_2870_ = 0;
v___x_2871_ = l_Lean_MessageData_withExprHover(v___y_2865_, v___x_2867_, v___x_2868_, v___x_2869_, v___x_2869_, v___x_2869_, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2866_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___x_2866_);
v___x_2874_ = lean_apply_2(v_toPure_2861_, lean_box(0), v___x_2873_);
return v___x_2874_;
}
v___jp_2875_:
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_val_2876_);
v___y_2865_ = v___x_2877_;
goto v___jp_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_2885_, lean_object* v_toPure_2886_, lean_object* v_firsts_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_toBind_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, lean_object* v___f_2893_, lean_object* v_env_2894_){
_start:
{
lean_object* v___y_2896_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = l_Lean_Environment_constants(v_env_2894_);
lean_inc(v_n_2885_);
v___x_2901_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_2891_, v___x_2892_, v___x_2900_, v_n_2885_);
lean_dec_ref(v___x_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2902_; 
lean_dec_ref(v___f_2893_);
v___x_2902_ = lean_box(0);
v___y_2896_ = v___x_2902_;
goto v___jp_2895_;
}
else
{
lean_object* v_val_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_val_2903_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2904_ = l_Lean_ConstantInfo_levelParams(v_val_2903_);
lean_dec(v_val_2903_);
v___x_2905_ = lean_box(0);
v___x_2906_ = l_List_mapTR_loop___redArg(v___f_2893_, v___x_2904_, v___x_2905_);
v___y_2896_ = v___x_2906_;
goto v___jp_2895_;
}
v___jp_2895_:
{
lean_object* v___f_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_inc(v_n_2885_);
v___f_2897_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2897_, 0, v_n_2885_);
lean_closure_set(v___f_2897_, 1, v___y_2896_);
lean_closure_set(v___f_2897_, 2, v_toPure_2886_);
lean_closure_set(v___f_2897_, 3, v_firsts_2887_);
v___x_2898_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_2888_, v_inst_2889_, v_n_2885_);
v___x_2899_ = lean_apply_4(v_toBind_2890_, lean_box(0), lean_box(0), v___x_2898_, v___f_2897_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_firsts_2910_, lean_object* v_n_2911_){
_start:
{
lean_object* v_toApplicative_2912_; lean_object* v_toBind_2913_; lean_object* v_getEnv_2914_; lean_object* v_toPure_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___f_2919_; lean_object* v___x_2920_; 
v_toApplicative_2912_ = lean_ctor_get(v_inst_2908_, 0);
v_toBind_2913_ = lean_ctor_get(v_inst_2908_, 1);
lean_inc_n(v_toBind_2913_, 2);
v_getEnv_2914_ = lean_ctor_get(v_inst_2909_, 0);
lean_inc(v_getEnv_2914_);
v_toPure_2915_ = lean_ctor_get(v_toApplicative_2912_, 1);
lean_inc(v_toPure_2915_);
v___f_2916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_2917_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2918_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_2919_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_2919_, 0, v_n_2911_);
lean_closure_set(v___f_2919_, 1, v_toPure_2915_);
lean_closure_set(v___f_2919_, 2, v_firsts_2910_);
lean_closure_set(v___f_2919_, 3, v_inst_2908_);
lean_closure_set(v___f_2919_, 4, v_inst_2909_);
lean_closure_set(v___f_2919_, 5, v_toBind_2913_);
lean_closure_set(v___f_2919_, 6, v___x_2917_);
lean_closure_set(v___f_2919_, 7, v___x_2918_);
lean_closure_set(v___f_2919_, 8, v___f_2916_);
v___x_2920_ = lean_apply_4(v_toBind_2913_, lean_box(0), lean_box(0), v_getEnv_2914_, v___f_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_firsts_2924_, lean_object* v_n_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_2922_, v_inst_2923_, v_firsts_2924_, v_n_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_2932_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_2936_);
lean_dec_ref(v_s_2936_);
return v_res_2937_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_2938_, lean_object* v_x1_2939_, lean_object* v_x2_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2941_ = l_Lean_Name_toString(v_x1_2939_, v___x_2938_);
v___x_2942_ = l_Lean_Name_toString(v_x2_2940_, v___x_2938_);
v___x_2943_ = lean_string_dec_lt(v___x_2941_, v___x_2942_);
lean_dec_ref(v___x_2942_);
lean_dec_ref(v___x_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_2944_, lean_object* v_x1_2945_, lean_object* v_x2_2946_){
_start:
{
uint8_t v___x_16971__boxed_2947_; uint8_t v_res_2948_; lean_object* v_r_2949_; 
v___x_16971__boxed_2947_ = lean_unbox(v___x_2944_);
v_res_2948_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16971__boxed_2947_, v_x1_2945_, v_x2_2946_);
v_r_2949_ = lean_box(v_res_2948_);
return v_r_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_2950_, lean_object* v_pivot_2951_, lean_object* v_as_2952_, lean_object* v_i_2953_, lean_object* v_k_2954_){
_start:
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_nat_dec_lt(v_k_2954_, v_hi_2950_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v_k_2954_);
lean_dec(v_pivot_2951_);
v___x_2956_ = lean_array_fswap(v_as_2952_, v_i_2953_, v_hi_2950_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_i_2953_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2958_ = lean_array_fget_borrowed(v_as_2952_, v_k_2954_);
lean_inc(v___x_2958_);
v___x_2959_ = l_Lean_Name_toString(v___x_2958_, v___x_2955_);
lean_inc(v_pivot_2951_);
v___x_2960_ = l_Lean_Name_toString(v_pivot_2951_, v___x_2955_);
v___x_2961_ = lean_string_dec_lt(v___x_2959_, v___x_2960_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v___x_2959_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_k_2954_, v___x_2962_);
lean_dec(v_k_2954_);
v_k_2954_ = v___x_2963_;
goto _start;
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2965_ = lean_array_fswap(v_as_2952_, v_i_2953_, v_k_2954_);
v___x_2966_ = lean_unsigned_to_nat(1u);
v___x_2967_ = lean_nat_add(v_i_2953_, v___x_2966_);
lean_dec(v_i_2953_);
v___x_2968_ = lean_nat_add(v_k_2954_, v___x_2966_);
lean_dec(v_k_2954_);
v_as_2952_ = v___x_2965_;
v_i_2953_ = v___x_2967_;
v_k_2954_ = v___x_2968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_2970_, lean_object* v_pivot_2971_, lean_object* v_as_2972_, lean_object* v_i_2973_, lean_object* v_k_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2970_, v_pivot_2971_, v_as_2972_, v_i_2973_, v_k_2974_);
lean_dec(v_hi_2970_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_2976_, lean_object* v_as_2977_, lean_object* v_lo_2978_, lean_object* v_hi_2979_){
_start:
{
lean_object* v___y_2981_; uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_lt(v_lo_2978_, v_hi_2979_);
if (v___x_2991_ == 0)
{
lean_dec(v_lo_2978_);
return v_as_2977_;
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_mid_2994_; lean_object* v___y_2996_; lean_object* v___y_3002_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_2992_ = lean_nat_add(v_lo_2978_, v_hi_2979_);
v___x_2993_ = lean_unsigned_to_nat(1u);
v_mid_2994_ = lean_nat_shiftr(v___x_2992_, v___x_2993_);
lean_dec(v___x_2992_);
v___x_3007_ = lean_array_fget_borrowed(v_as_2977_, v_mid_2994_);
v___x_3008_ = lean_array_fget_borrowed(v_as_2977_, v_lo_2978_);
lean_inc(v___x_3008_);
lean_inc(v___x_3007_);
v___x_3009_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2991_, v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
v___y_3002_ = v_as_2977_;
goto v___jp_3001_;
}
else
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_array_fswap(v_as_2977_, v_lo_2978_, v_mid_2994_);
v___y_3002_ = v___x_3010_;
goto v___jp_3001_;
}
v___jp_2995_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_array_fget_borrowed(v___y_2996_, v_mid_2994_);
v___x_2998_ = lean_array_fget_borrowed(v___y_2996_, v_hi_2979_);
lean_inc(v___x_2998_);
lean_inc(v___x_2997_);
v___x_2999_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2991_, v___x_2997_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_dec(v_mid_2994_);
v___y_2981_ = v___y_2996_;
goto v___jp_2980_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_array_fswap(v___y_2996_, v_mid_2994_, v_hi_2979_);
lean_dec(v_mid_2994_);
v___y_2981_ = v___x_3000_;
goto v___jp_2980_;
}
}
v___jp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3003_ = lean_array_fget_borrowed(v___y_3002_, v_hi_2979_);
v___x_3004_ = lean_array_fget_borrowed(v___y_3002_, v_lo_2978_);
lean_inc(v___x_3004_);
lean_inc(v___x_3003_);
v___x_3005_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2991_, v___x_3003_, v___x_3004_);
if (v___x_3005_ == 0)
{
v___y_2996_ = v___y_3002_;
goto v___jp_2995_;
}
else
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_array_fswap(v___y_3002_, v_lo_2978_, v_hi_2979_);
v___y_2996_ = v___x_3006_;
goto v___jp_2995_;
}
}
}
v___jp_2980_:
{
lean_object* v_pivot_2982_; lean_object* v___x_2983_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; uint8_t v___x_2986_; 
v_pivot_2982_ = lean_array_fget(v___y_2981_, v_hi_2979_);
lean_inc_n(v_lo_2978_, 2);
v___x_2983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2979_, v_pivot_2982_, v___y_2981_, v_lo_2978_, v_lo_2978_);
v_fst_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_fst_2984_);
v_snd_2985_ = lean_ctor_get(v___x_2983_, 1);
lean_inc(v_snd_2985_);
lean_dec_ref(v___x_2983_);
v___x_2986_ = lean_nat_dec_le(v_hi_2979_, v_fst_2984_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2976_, v_snd_2985_, v_lo_2978_, v_fst_2984_);
v___x_2988_ = lean_unsigned_to_nat(1u);
v___x_2989_ = lean_nat_add(v_fst_2984_, v___x_2988_);
lean_dec(v_fst_2984_);
v_as_2977_ = v___x_2987_;
v_lo_2978_ = v___x_2989_;
goto _start;
}
else
{
lean_dec(v_fst_2984_);
lean_dec(v_lo_2978_);
return v_snd_2985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_3011_, lean_object* v_as_3012_, lean_object* v_lo_3013_, lean_object* v_hi_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3011_, v_as_3012_, v_lo_3013_, v_hi_3014_);
lean_dec(v_hi_3014_);
lean_dec(v_n_3011_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_3016_, lean_object* v_x_3017_){
_start:
{
if (lean_obj_tag(v_x_3017_) == 0)
{
lean_object* v_k_3018_; lean_object* v_l_3019_; lean_object* v_r_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_k_3018_ = lean_ctor_get(v_x_3017_, 1);
lean_inc(v_k_3018_);
v_l_3019_ = lean_ctor_get(v_x_3017_, 3);
lean_inc(v_l_3019_);
v_r_3020_ = lean_ctor_get(v_x_3017_, 4);
lean_inc(v_r_3020_);
lean_dec_ref_known(v_x_3017_, 5);
v___x_3021_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_3016_, v_l_3019_);
v___x_3022_ = lean_array_push(v___x_3021_, v_k_3018_);
v_init_3016_ = v___x_3022_;
v_x_3017_ = v_r_3020_;
goto _start;
}
else
{
return v_init_3016_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
if (lean_obj_tag(v_a_3024_) == 0)
{
lean_object* v___x_3026_; 
v___x_3026_ = l_List_reverse___redArg(v_a_3025_);
return v___x_3026_;
}
else
{
lean_object* v_head_3027_; lean_object* v_tail_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3037_; 
v_head_3027_ = lean_ctor_get(v_a_3024_, 0);
v_tail_3028_ = lean_ctor_get(v_a_3024_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3030_ = v_a_3024_;
v_isShared_3031_ = v_isSharedCheck_3037_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_tail_3028_);
lean_inc(v_head_3027_);
lean_dec(v_a_3024_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3037_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = l_Lean_Level_param___override(v_head_3027_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v_a_3025_);
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_3025_);
v___x_3034_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
v_a_3024_ = v_tail_3028_;
v_a_3025_ = v___x_3034_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_3038_, lean_object* v_x2_3039_){
_start:
{
lean_object* v_fst_3040_; lean_object* v_fst_3041_; uint8_t v___x_3042_; 
v_fst_3040_ = lean_ctor_get(v_x1_3038_, 0);
v_fst_3041_ = lean_ctor_get(v_x2_3039_, 0);
v___x_3042_ = l_Lean_Name_quickLt(v_fst_3040_, v_fst_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_3043_, lean_object* v_x2_3044_){
_start:
{
uint8_t v_res_3045_; lean_object* v_r_3046_; 
v_res_3045_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_3043_, v_x2_3044_);
lean_dec_ref(v_x2_3044_);
lean_dec_ref(v_x1_3043_);
v_r_3046_ = lean_box(v_res_3045_);
return v_r_3046_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_3047_, lean_object* v_k_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_m_3053_; lean_object* v_a_3054_; uint8_t v___x_3055_; 
v___x_3051_ = lean_nat_add(v_x_3049_, v_x_3050_);
v___x_3052_ = lean_unsigned_to_nat(1u);
v_m_3053_ = lean_nat_shiftr(v___x_3051_, v___x_3052_);
lean_dec(v___x_3051_);
v_a_3054_ = lean_array_fget_borrowed(v_as_3047_, v_m_3053_);
v___x_3055_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_3054_, v_k_3048_);
if (v___x_3055_ == 0)
{
uint8_t v___x_3056_; 
lean_dec(v_x_3050_);
v___x_3056_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_3048_, v_a_3054_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_dec(v_m_3053_);
lean_dec(v_x_3049_);
lean_inc(v_a_3054_);
v___x_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_a_3054_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_nat_dec_eq(v_m_3053_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = lean_nat_sub(v_m_3053_, v___x_3052_);
lean_dec(v_m_3053_);
v___x_3061_ = lean_nat_dec_lt(v___x_3060_, v_x_3049_);
if (v___x_3061_ == 0)
{
v_x_3050_ = v___x_3060_;
goto _start;
}
else
{
lean_object* v___x_3063_; 
lean_dec(v___x_3060_);
lean_dec(v_x_3049_);
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
}
else
{
lean_object* v___x_3064_; 
lean_dec(v_m_3053_);
lean_dec(v_x_3049_);
v___x_3064_ = lean_box(0);
return v___x_3064_;
}
}
}
else
{
lean_object* v___x_3065_; uint8_t v___x_3066_; 
lean_dec(v_x_3049_);
v___x_3065_ = lean_nat_add(v_m_3053_, v___x_3052_);
lean_dec(v_m_3053_);
v___x_3066_ = lean_nat_dec_le(v___x_3065_, v_x_3050_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; 
lean_dec(v___x_3065_);
lean_dec(v_x_3050_);
v___x_3067_ = lean_box(0);
return v___x_3067_;
}
else
{
v_x_3049_ = v___x_3065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_3069_, lean_object* v_k_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3069_, v_k_3070_, v_x_3071_, v_x_3072_);
lean_dec_ref(v_k_3070_);
lean_dec_ref(v_as_3069_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_env_3082_; lean_object* v___x_3083_; 
v___x_3077_ = lean_box(1);
v___x_3078_ = lean_st_ref_get(v___y_3075_);
v_env_3082_ = lean_ctor_get(v___x_3078_, 0);
lean_inc_ref(v_env_3082_);
lean_dec(v___x_3078_);
v___x_3083_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3082_, v_tac_3074_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v___x_3084_; lean_object* v_toEnvExtension_3085_; lean_object* v_asyncMode_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3084_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3085_ = lean_ctor_get(v___x_3084_, 0);
v_asyncMode_3086_ = lean_ctor_get(v_toEnvExtension_3085_, 2);
v___x_3087_ = lean_box(0);
v___x_3088_ = 0;
v___x_3089_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3077_, v___x_3084_, v_env_3082_, v_asyncMode_3086_, v___x_3087_, v___x_3088_);
v___x_3090_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3089_, v_tac_3074_);
lean_dec(v_tac_3074_);
lean_dec(v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
else
{
lean_object* v_val_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3120_; 
v_val_3092_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3094_ = v___x_3083_;
v_isShared_3095_ = v_isSharedCheck_3120_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_val_3092_);
lean_dec(v___x_3083_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3120_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3096_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3097_ = 0;
v___x_3098_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3077_, v___x_3096_, v_env_3082_, v_val_3092_, v___x_3097_);
lean_dec(v_val_3092_);
lean_dec_ref(v_env_3082_);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_array_get_size(v___x_3098_);
v___x_3101_ = lean_nat_dec_lt(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec_ref(v___x_3098_);
lean_del_object(v___x_3094_);
lean_dec(v_tac_3074_);
goto v___jp_3079_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3102_ = lean_unsigned_to_nat(1u);
v___x_3103_ = lean_nat_sub(v___x_3100_, v___x_3102_);
v___x_3104_ = lean_nat_dec_le(v___x_3099_, v___x_3103_);
if (v___x_3104_ == 0)
{
lean_dec(v___x_3103_);
lean_dec_ref(v___x_3098_);
lean_del_object(v___x_3094_);
lean_dec(v_tac_3074_);
goto v___jp_3079_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_tac_3074_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_3098_, v___x_3106_, v___x_3099_, v___x_3103_);
lean_dec_ref_known(v___x_3106_, 2);
lean_dec_ref(v___x_3098_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_del_object(v___x_3094_);
goto v___jp_3079_;
}
else
{
lean_object* v_val_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3119_; 
v_val_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3119_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_val_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3119_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_snd_3112_; lean_object* v___x_3114_; 
v_snd_3112_ = lean_ctor_get(v_val_3108_, 1);
lean_inc(v_snd_3112_);
lean_dec(v_val_3108_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v_snd_3112_);
v___x_3114_ = v___x_3110_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_snd_3112_);
v___x_3114_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3114_);
v___x_3116_ = v___x_3094_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
}
}
}
v___jp_3079_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3121_, v___y_3122_);
lean_dec(v___y_3122_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_3125_, lean_object* v_k_3126_){
_start:
{
if (lean_obj_tag(v_t_3125_) == 0)
{
lean_object* v_k_3127_; lean_object* v_v_3128_; lean_object* v_l_3129_; lean_object* v_r_3130_; uint8_t v___x_3131_; 
v_k_3127_ = lean_ctor_get(v_t_3125_, 1);
v_v_3128_ = lean_ctor_get(v_t_3125_, 2);
v_l_3129_ = lean_ctor_get(v_t_3125_, 3);
v_r_3130_ = lean_ctor_get(v_t_3125_, 4);
v___x_3131_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3126_, v_k_3127_);
switch(v___x_3131_)
{
case 0:
{
v_t_3125_ = v_l_3129_;
goto _start;
}
case 1:
{
lean_object* v___x_3133_; 
lean_inc(v_v_3128_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_v_3128_);
return v___x_3133_;
}
default: 
{
v_t_3125_ = v_r_3130_;
goto _start;
}
}
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_box(0);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_3136_, lean_object* v_k_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3136_, v_k_3137_);
lean_dec(v_k_3137_);
lean_dec(v_t_3136_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_3139_, lean_object* v_x_3140_){
_start:
{
if (lean_obj_tag(v_x_3140_) == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_box(0);
return v___x_3141_;
}
else
{
lean_object* v_key_3142_; lean_object* v_value_3143_; lean_object* v_tail_3144_; uint8_t v___x_3145_; 
v_key_3142_ = lean_ctor_get(v_x_3140_, 0);
v_value_3143_ = lean_ctor_get(v_x_3140_, 1);
v_tail_3144_ = lean_ctor_get(v_x_3140_, 2);
v___x_3145_ = lean_name_eq(v_key_3142_, v_a_3139_);
if (v___x_3145_ == 0)
{
v_x_3140_ = v_tail_3144_;
goto _start;
}
else
{
lean_object* v___x_3147_; 
lean_inc(v_value_3143_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_value_3143_);
return v___x_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3148_, v_x_3149_);
lean_dec(v_x_3149_);
lean_dec(v_a_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_buckets_3153_; lean_object* v___x_3154_; uint64_t v___y_3156_; 
v_buckets_3153_ = lean_ctor_get(v_m_3151_, 1);
v___x_3154_ = lean_array_get_size(v_buckets_3153_);
if (lean_obj_tag(v_a_3152_) == 0)
{
uint64_t v___x_3170_; 
v___x_3170_ = 1723ULL;
v___y_3156_ = v___x_3170_;
goto v___jp_3155_;
}
else
{
uint64_t v_hash_3171_; 
v_hash_3171_ = lean_ctor_get_uint64(v_a_3152_, sizeof(void*)*2);
v___y_3156_ = v_hash_3171_;
goto v___jp_3155_;
}
v___jp_3155_:
{
uint64_t v___x_3157_; uint64_t v___x_3158_; uint64_t v_fold_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; uint64_t v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3157_ = 32ULL;
v___x_3158_ = lean_uint64_shift_right(v___y_3156_, v___x_3157_);
v_fold_3159_ = lean_uint64_xor(v___y_3156_, v___x_3158_);
v___x_3160_ = 16ULL;
v___x_3161_ = lean_uint64_shift_right(v_fold_3159_, v___x_3160_);
v___x_3162_ = lean_uint64_xor(v_fold_3159_, v___x_3161_);
v___x_3163_ = lean_uint64_to_usize(v___x_3162_);
v___x_3164_ = lean_usize_of_nat(v___x_3154_);
v___x_3165_ = ((size_t)1ULL);
v___x_3166_ = lean_usize_sub(v___x_3164_, v___x_3165_);
v___x_3167_ = lean_usize_land(v___x_3163_, v___x_3166_);
v___x_3168_ = lean_array_uget_borrowed(v_buckets_3153_, v___x_3167_);
v___x_3169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3152_, v___x_3168_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3172_, v_a_3173_);
lean_dec(v_a_3173_);
lean_dec_ref(v_m_3172_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_3175_, lean_object* v_vals_3176_, lean_object* v_i_3177_, lean_object* v_k_3178_){
_start:
{
lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = lean_array_get_size(v_keys_3175_);
v___x_3180_ = lean_nat_dec_lt(v_i_3177_, v___x_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec(v_i_3177_);
v___x_3181_ = lean_box(0);
return v___x_3181_;
}
else
{
lean_object* v_k_x27_3182_; uint8_t v___x_3183_; 
v_k_x27_3182_ = lean_array_fget_borrowed(v_keys_3175_, v_i_3177_);
v___x_3183_ = lean_name_eq(v_k_3178_, v_k_x27_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = lean_nat_add(v_i_3177_, v___x_3184_);
lean_dec(v_i_3177_);
v_i_3177_ = v___x_3185_;
goto _start;
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_array_fget_borrowed(v_vals_3176_, v_i_3177_);
lean_dec(v_i_3177_);
lean_inc(v___x_3187_);
v___x_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
return v___x_3188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_3189_, lean_object* v_vals_3190_, lean_object* v_i_3191_, lean_object* v_k_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3189_, v_vals_3190_, v_i_3191_, v_k_3192_);
lean_dec(v_k_3192_);
lean_dec_ref(v_vals_3190_);
lean_dec_ref(v_keys_3189_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3194_, size_t v_x_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 0)
{
lean_object* v_es_3197_; lean_object* v___x_3198_; size_t v___x_3199_; size_t v___x_3200_; lean_object* v_j_3201_; lean_object* v___x_3202_; 
v_es_3197_ = lean_ctor_get(v_x_3194_, 0);
v___x_3198_ = lean_box(2);
v___x_3199_ = ((size_t)31ULL);
v___x_3200_ = lean_usize_land(v_x_3195_, v___x_3199_);
v_j_3201_ = lean_usize_to_nat(v___x_3200_);
v___x_3202_ = lean_array_get_borrowed(v___x_3198_, v_es_3197_, v_j_3201_);
lean_dec(v_j_3201_);
switch(lean_obj_tag(v___x_3202_))
{
case 0:
{
lean_object* v_key_3203_; lean_object* v_val_3204_; uint8_t v___x_3205_; 
v_key_3203_ = lean_ctor_get(v___x_3202_, 0);
v_val_3204_ = lean_ctor_get(v___x_3202_, 1);
v___x_3205_ = lean_name_eq(v_x_3196_, v_key_3203_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_box(0);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; 
lean_inc(v_val_3204_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_val_3204_);
return v___x_3207_;
}
}
case 1:
{
lean_object* v_node_3208_; size_t v___x_3209_; size_t v___x_3210_; 
v_node_3208_ = lean_ctor_get(v___x_3202_, 0);
v___x_3209_ = ((size_t)5ULL);
v___x_3210_ = lean_usize_shift_right(v_x_3195_, v___x_3209_);
v_x_3194_ = v_node_3208_;
v_x_3195_ = v___x_3210_;
goto _start;
}
default: 
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_box(0);
return v___x_3212_;
}
}
}
else
{
lean_object* v_ks_3213_; lean_object* v_vs_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_ks_3213_ = lean_ctor_get(v_x_3194_, 0);
v_vs_3214_ = lean_ctor_get(v_x_3194_, 1);
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_3213_, v_vs_3214_, v___x_3215_, v_x_3196_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_3217_, lean_object* v_x_3218_, lean_object* v_x_3219_){
_start:
{
size_t v_x_17344__boxed_3220_; lean_object* v_res_3221_; 
v_x_17344__boxed_3220_ = lean_unbox_usize(v_x_3218_);
lean_dec(v_x_3218_);
v_res_3221_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3217_, v_x_17344__boxed_3220_, v_x_3219_);
lean_dec(v_x_3219_);
lean_dec_ref(v_x_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
uint64_t v___y_3225_; 
if (lean_obj_tag(v_x_3223_) == 0)
{
uint64_t v___x_3228_; 
v___x_3228_ = 1723ULL;
v___y_3225_ = v___x_3228_;
goto v___jp_3224_;
}
else
{
uint64_t v_hash_3229_; 
v_hash_3229_ = lean_ctor_get_uint64(v_x_3223_, sizeof(void*)*2);
v___y_3225_ = v_hash_3229_;
goto v___jp_3224_;
}
v___jp_3224_:
{
size_t v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_uint64_to_usize(v___y_3225_);
v___x_3227_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3222_, v___x_3226_, v_x_3223_);
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3230_, v_x_3231_);
lean_dec(v_x_3231_);
lean_dec_ref(v_x_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
uint8_t v_stage_u2081_3235_; 
v_stage_u2081_3235_ = lean_ctor_get_uint8(v_x_3233_, sizeof(void*)*2);
if (v_stage_u2081_3235_ == 0)
{
lean_object* v_map_u2081_3236_; lean_object* v_map_u2082_3237_; lean_object* v___x_3238_; 
v_map_u2081_3236_ = lean_ctor_get(v_x_3233_, 0);
v_map_u2082_3237_ = lean_ctor_get(v_x_3233_, 1);
v___x_3238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3236_, v_x_3234_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_3237_, v_x_3234_);
return v___x_3239_;
}
else
{
return v___x_3238_;
}
}
else
{
lean_object* v_map_u2081_3240_; lean_object* v___x_3241_; 
v_map_u2081_3240_ = lean_ctor_get(v_x_3233_, 0);
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3240_, v_x_3234_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_3242_, lean_object* v_x_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3242_, v_x_3243_);
lean_dec(v_x_3243_);
lean_dec_ref(v_x_3242_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_3245_, lean_object* v_n_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3265_; lean_object* v_val_3266_; lean_object* v___x_3268_; lean_object* v___y_3270_; lean_object* v_env_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3268_ = lean_st_ref_get(v___y_3248_);
v_env_3285_ = lean_ctor_get(v___x_3268_, 0);
lean_inc_ref(v_env_3285_);
lean_dec(v___x_3268_);
v___x_3286_ = l_Lean_Environment_constants(v_env_3285_);
v___x_3287_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_3286_, v_n_3246_);
lean_dec_ref(v___x_3286_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_box(0);
v___y_3270_ = v___x_3288_;
goto v___jp_3269_;
}
else
{
lean_object* v_val_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_val_3289_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_val_3289_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3290_ = l_Lean_ConstantInfo_levelParams(v_val_3289_);
lean_dec(v_val_3289_);
v___x_3291_ = lean_box(0);
v___x_3292_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_3290_, v___x_3291_);
v___y_3270_ = v___x_3292_;
goto v___jp_3269_;
}
v___jp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3253_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_3254_ = l_Lean_Expr_const___override(v_n_3246_, v___y_3251_);
v___x_3255_ = lean_unsigned_to_nat(32u);
v___x_3256_ = lean_mk_empty_array_with_capacity(v___x_3255_);
lean_dec_ref(v___x_3256_);
v___x_3257_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3258_ = lean_box(0);
v___x_3259_ = 0;
v___x_3260_ = l_Lean_MessageData_withExprHover(v___y_3252_, v___x_3254_, v___x_3257_, v___x_3258_, v___x_3258_, v___x_3258_, v___x_3259_);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3253_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___x_3253_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
v___jp_3264_:
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_val_3266_);
v___y_3251_ = v___y_3265_;
v___y_3252_ = v___x_3267_;
goto v___jp_3250_;
}
v___jp_3269_:
{
lean_object* v___x_3271_; lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3284_; 
lean_inc(v_n_3246_);
v___x_3271_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_3246_, v___y_3248_);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3284_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3284_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
if (lean_obj_tag(v_a_3272_) == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_3245_, v_n_3246_);
if (lean_obj_tag(v___x_3276_) == 0)
{
uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3277_ = 1;
lean_inc(v_n_3246_);
v___x_3278_ = l_Lean_Name_toString(v_n_3246_, v___x_3277_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set_tag(v___x_3274_, 3);
lean_ctor_set(v___x_3274_, 0, v___x_3278_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
v___y_3251_ = v___y_3270_;
v___y_3252_ = v___x_3280_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_val_3282_; 
lean_del_object(v___x_3274_);
v_val_3282_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v___x_3276_, 1);
v___y_3265_ = v___y_3270_;
v_val_3266_ = v_val_3282_;
goto v___jp_3264_;
}
}
else
{
lean_object* v_val_3283_; 
lean_del_object(v___x_3274_);
v_val_3283_ = lean_ctor_get(v_a_3272_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v_a_3272_, 1);
v___y_3265_ = v___y_3270_;
v_val_3266_ = v_val_3283_;
goto v___jp_3264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_3293_, lean_object* v_n_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3293_, v_n_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v_firsts_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
if (lean_obj_tag(v_x_3300_) == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = l_List_reverse___redArg(v_x_3301_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
else
{
lean_object* v_head_3307_; lean_object* v_tail_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3326_; 
v_head_3307_ = lean_ctor_get(v_x_3300_, 0);
v_tail_3308_ = lean_ctor_get(v_x_3300_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_x_3300_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3310_ = v_x_3300_;
v_isShared_3311_ = v_isSharedCheck_3326_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_tail_3308_);
lean_inc(v_head_3307_);
lean_dec(v_x_3300_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3326_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_3299_, v_head_3307_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3315_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 1, v_x_3301_);
lean_ctor_set(v___x_3310_, 0, v_a_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3313_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_x_3301_);
v___x_3315_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
v_x_3300_ = v_tail_3308_;
v_x_3301_ = v___x_3315_;
goto _start;
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_del_object(v___x_3310_);
lean_dec(v_tail_3308_);
lean_dec(v_x_3301_);
v_a_3318_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3312_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3312_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3327_, v_x_3328_, v_x_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v_a_3327_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_3334_, lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v_a_3337_, lean_object* v_b_3338_){
_start:
{
lean_object* v_it_3340_; lean_object* v_startInclusive_3341_; lean_object* v_endExclusive_3342_; 
if (lean_obj_tag(v_a_3337_) == 0)
{
lean_object* v_currPos_3347_; lean_object* v_searcher_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3371_; 
v_currPos_3347_ = lean_ctor_get(v_a_3337_, 0);
v_searcher_3348_ = lean_ctor_get(v_a_3337_, 1);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_a_3337_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3350_ = v_a_3337_;
v_isShared_3351_ = v_isSharedCheck_3371_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_searcher_3348_);
lean_inc(v_currPos_3347_);
lean_dec(v_a_3337_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3371_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
uint8_t v_decide_3352_; 
v_decide_3352_ = lean_nat_dec_eq(v_searcher_3348_, v___x_3336_);
if (v_decide_3352_ == 0)
{
uint32_t v___x_3353_; uint32_t v___x_3354_; uint8_t v___x_3355_; 
v___x_3353_ = 10;
v___x_3354_ = lean_string_utf8_get_fast(v_val_3334_, v_searcher_3348_);
v___x_3355_ = lean_uint32_dec_eq(v___x_3354_, v___x_3353_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = lean_string_utf8_next_fast(v_val_3334_, v_searcher_3348_);
lean_dec(v_searcher_3348_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 1, v___x_3356_);
v___x_3358_ = v___x_3350_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_currPos_3347_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
v_a_3337_ = v___x_3358_;
goto _start;
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v_slice_3364_; lean_object* v_nextIt_3366_; 
v___x_3361_ = lean_string_utf8_next_fast(v_val_3334_, v_searcher_3348_);
v___x_3362_ = lean_nat_sub(v___x_3361_, v_searcher_3348_);
v___x_3363_ = lean_nat_add(v_searcher_3348_, v___x_3362_);
lean_dec(v___x_3362_);
v_slice_3364_ = l_String_Slice_subslice_x21(v___x_3335_, v_currPos_3347_, v_searcher_3348_);
lean_inc(v___x_3363_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 1, v___x_3363_);
lean_ctor_set(v___x_3350_, 0, v___x_3363_);
v_nextIt_3366_ = v___x_3350_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3363_);
v_nextIt_3366_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v_startInclusive_3367_; lean_object* v_endExclusive_3368_; 
v_startInclusive_3367_ = lean_ctor_get(v_slice_3364_, 0);
lean_inc(v_startInclusive_3367_);
v_endExclusive_3368_ = lean_ctor_get(v_slice_3364_, 1);
lean_inc(v_endExclusive_3368_);
lean_dec_ref(v_slice_3364_);
v_it_3340_ = v_nextIt_3366_;
v_startInclusive_3341_ = v_startInclusive_3367_;
v_endExclusive_3342_ = v_endExclusive_3368_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v___x_3370_; 
lean_del_object(v___x_3350_);
lean_dec(v_searcher_3348_);
v___x_3370_ = lean_box(1);
lean_inc(v___x_3336_);
v_it_3340_ = v___x_3370_;
v_startInclusive_3341_ = v_currPos_3347_;
v_endExclusive_3342_ = v___x_3336_;
goto v___jp_3339_;
}
}
}
else
{
lean_dec(v___x_3336_);
return v_b_3338_;
}
v___jp_3339_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_string_utf8_extract_fast(v_val_3334_, v_startInclusive_3341_, v_endExclusive_3342_);
lean_dec(v_endExclusive_3342_);
lean_dec(v_startInclusive_3341_);
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
v___x_3345_ = lean_array_push(v_b_3338_, v___x_3344_);
v_a_3337_ = v_it_3340_;
v_b_3338_ = v___x_3345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_3372_, lean_object* v___x_3373_, lean_object* v___x_3374_, lean_object* v_a_3375_, lean_object* v_b_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3372_, v___x_3373_, v___x_3374_, v_a_3375_, v_b_3376_);
lean_dec_ref(v___x_3373_);
lean_dec_ref(v_val_3372_);
return v_res_3377_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_3393_ = l_Lean_MessageData_ofFormat(v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = l_List_reverse___redArg(v_x_3397_);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
else
{
lean_object* v_head_3403_; lean_object* v_tail_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3501_; 
v_head_3403_ = lean_ctor_get(v_x_3396_, 0);
v_tail_3404_ = lean_ctor_get(v_x_3396_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_x_3396_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3406_ = v_x_3396_;
v_isShared_3407_ = v_isSharedCheck_3501_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_tail_3404_);
lean_inc(v_head_3403_);
lean_dec(v_x_3396_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3501_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v_snd_3421_; lean_object* v_fst_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3500_; 
v_snd_3421_ = lean_ctor_get(v_head_3403_, 1);
v_fst_3422_ = lean_ctor_get(v_head_3403_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_head_3403_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3424_ = v_head_3403_;
v_isShared_3425_ = v_isSharedCheck_3500_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3422_);
lean_dec(v_head_3403_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3500_;
goto v_resetjp_3423_;
}
v___jp_3408_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___y_3409_);
lean_ctor_set(v___x_3413_, 1, v___y_3412_);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___y_3411_);
v___x_3415_ = l_Lean_MessageData_nestD(v___x_3414_);
lean_inc_ref(v___y_3410_);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___y_3410_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v_x_3397_);
lean_ctor_set(v___x_3406_, 0, v___x_3416_);
v___x_3418_ = v___x_3406_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_x_3397_);
v___x_3418_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
v_x_3396_ = v_tail_3404_;
v_x_3397_ = v___x_3418_;
goto _start;
}
}
v_resetjp_3423_:
{
lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3499_; 
v_fst_3426_ = lean_ctor_get(v_snd_3421_, 0);
v_snd_3427_ = lean_ctor_get(v_snd_3421_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3429_ = v_snd_3421_;
v_isShared_3430_ = v_isSharedCheck_3499_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v_snd_3421_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3499_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v_a_3454_; lean_object* v___y_3470_; lean_object* v___x_3479_; 
v___x_3479_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3395_, v_fst_3422_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_MessageData_nil;
v_a_3454_ = v___x_3480_;
goto v___jp_3453_;
}
else
{
lean_object* v_val_3481_; 
v_val_3481_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v___x_3479_, 1);
if (lean_obj_tag(v_val_3481_) == 0)
{
lean_object* v_size_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v_size_3482_ = lean_ctor_get(v_val_3481_, 0);
v___x_3483_ = lean_mk_empty_array_with_capacity(v_size_3482_);
v___x_3484_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_3483_, v_val_3481_);
v___x_3485_ = lean_array_get_size(v___x_3484_);
v___x_3490_ = lean_unsigned_to_nat(0u);
v___x_3491_ = lean_nat_dec_eq(v___x_3485_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___y_3495_; uint8_t v___x_3497_; 
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_nat_sub(v___x_3485_, v___x_3492_);
v___x_3497_ = lean_nat_dec_le(v___x_3490_, v___x_3493_);
if (v___x_3497_ == 0)
{
lean_inc(v___x_3493_);
v___y_3495_ = v___x_3493_;
goto v___jp_3494_;
}
else
{
v___y_3495_ = v___x_3490_;
goto v___jp_3494_;
}
v___jp_3494_:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_nat_dec_le(v___y_3495_, v___x_3493_);
if (v___x_3496_ == 0)
{
lean_dec(v___x_3493_);
lean_inc(v___y_3495_);
v___y_3487_ = v___y_3495_;
v___y_3488_ = v___y_3495_;
goto v___jp_3486_;
}
else
{
v___y_3487_ = v___y_3495_;
v___y_3488_ = v___x_3493_;
goto v___jp_3486_;
}
}
}
else
{
v___y_3470_ = v___x_3484_;
goto v___jp_3469_;
}
v___jp_3486_:
{
lean_object* v___x_3489_; 
v___x_3489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_3485_, v___x_3484_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
v___y_3470_ = v___x_3489_;
goto v___jp_3469_;
}
}
else
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_MessageData_nil;
v_a_3454_ = v___x_3498_;
goto v___jp_3453_;
}
}
v___jp_3431_:
{
lean_object* v___x_3437_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 7);
lean_ctor_set(v___x_3429_, 1, v___y_3435_);
lean_ctor_set(v___x_3429_, 0, v___y_3433_);
v___x_3437_ = v___x_3429_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___y_3433_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v___y_3435_);
v___x_3437_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
if (lean_obj_tag(v_snd_3427_) == 0)
{
lean_object* v___x_3438_; 
lean_del_object(v___x_3424_);
v___x_3438_ = l_Lean_MessageData_nil;
v___y_3409_ = v___x_3437_;
v___y_3410_ = v___y_3432_;
v___y_3411_ = v___y_3434_;
v___y_3412_ = v___x_3438_;
goto v___jp_3408_;
}
else
{
lean_object* v_val_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v_val_3439_ = lean_ctor_get(v_snd_3427_, 0);
lean_inc_n(v_val_3439_, 2);
lean_dec_ref_known(v_snd_3427_, 1);
v___x_3440_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3441_ = lean_unsigned_to_nat(0u);
v___x_3442_ = lean_string_utf8_byte_size(v_val_3439_);
v___x_3443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3443_, 0, v_val_3439_);
lean_ctor_set(v___x_3443_, 1, v___x_3441_);
lean_ctor_set(v___x_3443_, 2, v___x_3442_);
v___x_3444_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_3445_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_3446_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3439_, v___x_3443_, v___x_3442_, v___x_3444_, v___x_3445_);
lean_dec_ref_known(v___x_3443_, 3);
lean_dec(v_val_3439_);
v___x_3447_ = lean_array_to_list(v___x_3446_);
v___x_3448_ = l_Lean_MessageData_joinSep(v___x_3447_, v___x_3440_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 7);
lean_ctor_set(v___x_3424_, 1, v___x_3448_);
lean_ctor_set(v___x_3424_, 0, v___x_3440_);
v___x_3450_ = v___x_3424_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
v___y_3409_ = v___x_3437_;
v___y_3410_ = v___y_3432_;
v___y_3411_ = v___y_3434_;
v___y_3412_ = v___x_3450_;
goto v___jp_3408_;
}
}
}
}
v___jp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3455_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_3456_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
lean_inc(v_fst_3422_);
v___x_3457_ = l_Lean_MessageData_ofName(v_fst_3422_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v___x_3456_);
v___x_3460_ = 1;
v___x_3461_ = l_Lean_Name_toString(v_fst_3422_, v___x_3460_);
v___x_3462_ = lean_string_dec_eq(v___x_3461_, v_fst_3426_);
lean_dec_ref(v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3463_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_3464_ = l_Lean_stringToMessageData(v_fst_3426_);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___y_3432_ = v___x_3455_;
v___y_3433_ = v___x_3459_;
v___y_3434_ = v_a_3454_;
v___y_3435_ = v___x_3467_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3468_; 
lean_dec(v_fst_3426_);
v___x_3468_ = l_Lean_MessageData_nil;
v___y_3432_ = v___x_3455_;
v___y_3433_ = v___x_3459_;
v___y_3434_ = v_a_3454_;
v___y_3435_ = v___x_3468_;
goto v___jp_3431_;
}
}
v___jp_3469_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_array_to_list(v___y_3470_);
v___x_3472_ = lean_box(0);
v___x_3473_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3394_, v___x_3471_, v___x_3472_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___x_3475_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3476_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_3477_ = l_Lean_MessageData_joinSep(v_a_3474_, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3475_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v_a_3454_ = v___x_3478_;
goto v___jp_3453_;
}
else
{
lean_del_object(v___x_3429_);
lean_dec(v_snd_3427_);
lean_dec(v_fst_3426_);
lean_del_object(v___x_3424_);
lean_dec(v_fst_3422_);
lean_del_object(v___x_3406_);
lean_dec(v_tail_3404_);
lean_dec(v_x_3397_);
return v___x_3473_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_x_3504_, lean_object* v_x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3502_, v_a_3503_, v_x_3504_, v_x_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v_a_3503_);
lean_dec(v_a_3502_);
return v_res_3509_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_3511_, uint8_t v___y_3512_, lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 1)
{
lean_object* v_pre_3514_; 
v_pre_3514_ = lean_ctor_get(v_x_3513_, 0);
if (lean_obj_tag(v_pre_3514_) == 0)
{
lean_object* v_str_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v_str_3515_ = lean_ctor_get(v_x_3513_, 1);
v___x_3516_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_3517_ = lean_string_dec_eq(v_str_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
return v___x_3517_;
}
else
{
return v_suppressElabErrors_3511_;
}
}
else
{
return v___y_3512_;
}
}
else
{
return v___y_3512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_3518_, lean_object* v___y_3519_, lean_object* v_x_3520_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3521_; uint8_t v___y_17960__boxed_3522_; uint8_t v_res_3523_; lean_object* v_r_3524_; 
v_suppressElabErrors_boxed_3521_ = lean_unbox(v_suppressElabErrors_3518_);
v___y_17960__boxed_3522_ = lean_unbox(v___y_3519_);
v_res_3523_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_3521_, v___y_17960__boxed_3522_, v_x_3520_);
lean_dec(v_x_3520_);
v_r_3524_ = lean_box(v_res_3523_);
return v_r_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_3525_, lean_object* v_msgData_3526_, uint8_t v_severity_3527_, uint8_t v_isSilent_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; uint8_t v___y_3598_; uint8_t v___y_3599_; uint8_t v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3626_; lean_object* v___y_3627_; uint8_t v___y_3628_; uint8_t v___y_3629_; lean_object* v___y_3630_; uint8_t v___y_3634_; uint8_t v___y_3635_; uint8_t v___y_3636_; uint8_t v___x_3651_; uint8_t v___y_3653_; uint8_t v___y_3654_; uint8_t v___y_3655_; uint8_t v___y_3657_; uint8_t v___x_3669_; 
v___x_3651_ = 2;
v___x_3669_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3527_, v___x_3651_);
if (v___x_3669_ == 0)
{
v___y_3657_ = v___x_3669_;
goto v___jp_3656_;
}
else
{
uint8_t v___x_3670_; 
lean_inc_ref(v_msgData_3526_);
v___x_3670_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3526_);
v___y_3657_ = v___x_3670_;
goto v___jp_3656_;
}
v___jp_3532_:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Elab_Command_getScope___redArg(v___y_3540_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v_currNamespace_3543_; lean_object* v___x_3544_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v_currNamespace_3543_ = lean_ctor_get(v_a_3542_, 2);
lean_inc(v_currNamespace_3543_);
lean_dec(v_a_3542_);
v___x_3544_ = l_Lean_Elab_Command_getScope___redArg(v___y_3540_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3580_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3580_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3580_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_openDecls_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v_env_3554_; lean_object* v_messages_3555_; lean_object* v_scopes_3556_; lean_object* v_usedQuotCtxts_3557_; lean_object* v_nextMacroScope_3558_; lean_object* v_maxRecDepth_3559_; lean_object* v_ngen_3560_; lean_object* v_auxDeclNGen_3561_; lean_object* v_infoState_3562_; lean_object* v_traceState_3563_; lean_object* v_snapshotTasks_3564_; lean_object* v_prevLinterStates_3565_; lean_object* v_codeQualityEntryTasks_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3579_; 
v_openDecls_3549_ = lean_ctor_get(v_a_3545_, 3);
lean_inc(v_openDecls_3549_);
lean_dec(v_a_3545_);
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v_currNamespace_3543_);
lean_ctor_set(v___x_3550_, 1, v_openDecls_3549_);
v___x_3551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___y_3535_);
lean_inc_ref(v___y_3539_);
lean_inc_ref(v___y_3538_);
v___x_3552_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3552_, 0, v___y_3538_);
lean_ctor_set(v___x_3552_, 1, v___y_3536_);
lean_ctor_set(v___x_3552_, 2, v___y_3534_);
lean_ctor_set(v___x_3552_, 3, v___y_3539_);
lean_ctor_set(v___x_3552_, 4, v___x_3551_);
lean_ctor_set_uint8(v___x_3552_, sizeof(void*)*5, v___y_3537_);
lean_ctor_set_uint8(v___x_3552_, sizeof(void*)*5 + 1, v___y_3533_);
lean_ctor_set_uint8(v___x_3552_, sizeof(void*)*5 + 2, v_isSilent_3528_);
v___x_3553_ = lean_st_ref_take(v___y_3540_);
v_env_3554_ = lean_ctor_get(v___x_3553_, 0);
v_messages_3555_ = lean_ctor_get(v___x_3553_, 1);
v_scopes_3556_ = lean_ctor_get(v___x_3553_, 2);
v_usedQuotCtxts_3557_ = lean_ctor_get(v___x_3553_, 3);
v_nextMacroScope_3558_ = lean_ctor_get(v___x_3553_, 4);
v_maxRecDepth_3559_ = lean_ctor_get(v___x_3553_, 5);
v_ngen_3560_ = lean_ctor_get(v___x_3553_, 6);
v_auxDeclNGen_3561_ = lean_ctor_get(v___x_3553_, 7);
v_infoState_3562_ = lean_ctor_get(v___x_3553_, 8);
v_traceState_3563_ = lean_ctor_get(v___x_3553_, 9);
v_snapshotTasks_3564_ = lean_ctor_get(v___x_3553_, 10);
v_prevLinterStates_3565_ = lean_ctor_get(v___x_3553_, 11);
v_codeQualityEntryTasks_3566_ = lean_ctor_get(v___x_3553_, 12);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3568_ = v___x_3553_;
v_isShared_3569_ = v_isSharedCheck_3579_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3566_);
lean_inc(v_prevLinterStates_3565_);
lean_inc(v_snapshotTasks_3564_);
lean_inc(v_traceState_3563_);
lean_inc(v_infoState_3562_);
lean_inc(v_auxDeclNGen_3561_);
lean_inc(v_ngen_3560_);
lean_inc(v_maxRecDepth_3559_);
lean_inc(v_nextMacroScope_3558_);
lean_inc(v_usedQuotCtxts_3557_);
lean_inc(v_scopes_3556_);
lean_inc(v_messages_3555_);
lean_inc(v_env_3554_);
lean_dec(v___x_3553_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3579_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3570_ = lean_box(0);
v___x_3571_ = l_Lean_MessageLog_add(v___x_3552_, v_messages_3555_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 1, v___x_3571_);
v___x_3573_ = v___x_3568_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_env_3554_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_scopes_3556_);
lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_usedQuotCtxts_3557_);
lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_nextMacroScope_3558_);
lean_ctor_set(v_reuseFailAlloc_3578_, 5, v_maxRecDepth_3559_);
lean_ctor_set(v_reuseFailAlloc_3578_, 6, v_ngen_3560_);
lean_ctor_set(v_reuseFailAlloc_3578_, 7, v_auxDeclNGen_3561_);
lean_ctor_set(v_reuseFailAlloc_3578_, 8, v_infoState_3562_);
lean_ctor_set(v_reuseFailAlloc_3578_, 9, v_traceState_3563_);
lean_ctor_set(v_reuseFailAlloc_3578_, 10, v_snapshotTasks_3564_);
lean_ctor_set(v_reuseFailAlloc_3578_, 11, v_prevLinterStates_3565_);
lean_ctor_set(v_reuseFailAlloc_3578_, 12, v_codeQualityEntryTasks_3566_);
v___x_3573_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3574_ = lean_st_ref_put(v___y_3540_, v___x_3573_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3570_);
v___x_3576_ = v___x_3547_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3570_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_currNamespace_3543_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
v_a_3581_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3544_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3544_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
v_a_3589_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3541_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3541_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
v___jp_3597_:
{
lean_object* v_fileName_3603_; lean_object* v_fileMap_3604_; uint8_t v_suppressElabErrors_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3624_; 
v_fileName_3603_ = lean_ctor_get(v___y_3529_, 0);
v_fileMap_3604_ = lean_ctor_get(v___y_3529_, 1);
v_suppressElabErrors_3605_ = lean_ctor_get_uint8(v___y_3529_, sizeof(void*)*10);
v___x_3606_ = lean_box(v_suppressElabErrors_3605_);
v___x_3607_ = lean_box(v___y_3598_);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3608_, 0, v___x_3606_);
lean_closure_set(v___f_3608_, 1, v___x_3607_);
v___x_3609_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3526_);
v___x_3610_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v___x_3609_, v___y_3530_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3624_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3624_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_inc_ref_n(v_fileMap_3604_, 2);
v___x_3615_ = l_Lean_FileMap_toPosition(v_fileMap_3604_, v___y_3601_);
lean_dec(v___y_3601_);
v___x_3616_ = l_Lean_FileMap_toPosition(v_fileMap_3604_, v___y_3602_);
lean_dec(v___y_3602_);
v___x_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
v___x_3618_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_suppressElabErrors_3605_ == 0)
{
lean_del_object(v___x_3613_);
lean_dec_ref(v___f_3608_);
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___x_3617_;
v___y_3535_ = v_a_3611_;
v___y_3536_ = v___x_3615_;
v___y_3537_ = v___y_3600_;
v___y_3538_ = v_fileName_3603_;
v___y_3539_ = v___x_3618_;
v___y_3540_ = v___y_3530_;
goto v___jp_3532_;
}
else
{
uint8_t v___x_3619_; 
lean_inc(v_a_3611_);
v___x_3619_ = l_Lean_MessageData_hasTag(v___f_3608_, v_a_3611_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec_ref_known(v___x_3617_, 1);
lean_dec_ref(v___x_3615_);
lean_dec(v_a_3611_);
v___x_3620_ = lean_box(0);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3620_);
v___x_3622_ = v___x_3613_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
else
{
lean_del_object(v___x_3613_);
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___x_3617_;
v___y_3535_ = v_a_3611_;
v___y_3536_ = v___x_3615_;
v___y_3537_ = v___y_3600_;
v___y_3538_ = v_fileName_3603_;
v___y_3539_ = v___x_3618_;
v___y_3540_ = v___y_3530_;
goto v___jp_3532_;
}
}
}
}
v___jp_3625_:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_Syntax_getTailPos_x3f(v___y_3627_, v___y_3629_);
lean_dec(v___y_3627_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_inc(v___y_3630_);
v___y_3598_ = v___y_3626_;
v___y_3599_ = v___y_3628_;
v___y_3600_ = v___y_3629_;
v___y_3601_ = v___y_3630_;
v___y_3602_ = v___y_3630_;
goto v___jp_3597_;
}
else
{
lean_object* v_val_3632_; 
v_val_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_val_3632_);
lean_dec_ref_known(v___x_3631_, 1);
v___y_3598_ = v___y_3626_;
v___y_3599_ = v___y_3628_;
v___y_3600_ = v___y_3629_;
v___y_3601_ = v___y_3630_;
v___y_3602_ = v_val_3632_;
goto v___jp_3597_;
}
}
v___jp_3633_:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Elab_Command_getRef___redArg(v___y_3529_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_ref_3639_; lean_object* v___x_3640_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_ref_3639_ = l_Lean_replaceRef(v_ref_3525_, v_a_3638_);
lean_dec(v_a_3638_);
v___x_3640_ = l_Lean_Syntax_getPos_x3f(v_ref_3639_, v___y_3635_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_unsigned_to_nat(0u);
v___y_3626_ = v___y_3634_;
v___y_3627_ = v_ref_3639_;
v___y_3628_ = v___y_3636_;
v___y_3629_ = v___y_3635_;
v___y_3630_ = v___x_3641_;
goto v___jp_3625_;
}
else
{
lean_object* v_val_3642_; 
v_val_3642_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v___x_3640_, 1);
v___y_3626_ = v___y_3634_;
v___y_3627_ = v_ref_3639_;
v___y_3628_ = v___y_3636_;
v___y_3629_ = v___y_3635_;
v___y_3630_ = v_val_3642_;
goto v___jp_3625_;
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec_ref(v_msgData_3526_);
v_a_3643_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3637_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3637_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
v___jp_3652_:
{
if (v___y_3655_ == 0)
{
v___y_3634_ = v___y_3653_;
v___y_3635_ = v___y_3654_;
v___y_3636_ = v_severity_3527_;
goto v___jp_3633_;
}
else
{
v___y_3634_ = v___y_3653_;
v___y_3635_ = v___y_3654_;
v___y_3636_ = v___x_3651_;
goto v___jp_3633_;
}
}
v___jp_3656_:
{
if (v___y_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v_scopes_3660_; lean_object* v___x_3661_; lean_object* v_opts_3662_; uint8_t v___x_3663_; uint8_t v___x_3664_; 
v___x_3658_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3659_ = lean_st_ref_get(v___y_3530_);
v_scopes_3660_ = lean_ctor_get(v___x_3659_, 2);
lean_inc(v_scopes_3660_);
lean_dec(v___x_3659_);
v___x_3661_ = l_List_head_x21___redArg(v___x_3658_, v_scopes_3660_);
lean_dec(v_scopes_3660_);
v_opts_3662_ = lean_ctor_get(v___x_3661_, 1);
lean_inc_ref(v_opts_3662_);
lean_dec(v___x_3661_);
v___x_3663_ = 1;
v___x_3664_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3527_, v___x_3663_);
if (v___x_3664_ == 0)
{
lean_dec_ref(v_opts_3662_);
v___y_3653_ = v___y_3657_;
v___y_3654_ = v___y_3657_;
v___y_3655_ = v___x_3664_;
goto v___jp_3652_;
}
else
{
lean_object* v___x_3665_; uint8_t v___x_3666_; 
v___x_3665_ = l_Lean_warningAsError;
v___x_3666_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_3662_, v___x_3665_);
lean_dec_ref(v_opts_3662_);
v___y_3653_ = v___y_3657_;
v___y_3654_ = v___y_3657_;
v___y_3655_ = v___x_3666_;
goto v___jp_3652_;
}
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
lean_dec_ref(v_msgData_3526_);
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_3671_, lean_object* v_msgData_3672_, lean_object* v_severity_3673_, lean_object* v_isSilent_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v_severity_boxed_3678_; uint8_t v_isSilent_boxed_3679_; lean_object* v_res_3680_; 
v_severity_boxed_3678_ = lean_unbox(v_severity_3673_);
v_isSilent_boxed_3679_ = lean_unbox(v_isSilent_3674_);
v_res_3680_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3671_, v_msgData_3672_, v_severity_boxed_3678_, v_isSilent_boxed_3679_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v_ref_3671_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_3681_, uint8_t v_severity_3682_, uint8_t v_isSilent_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_Elab_Command_getRef___redArg(v___y_3684_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_3688_, v_msgData_3681_, v_severity_3682_, v_isSilent_3683_, v___y_3684_, v___y_3685_);
lean_dec(v_a_3688_);
return v___x_3689_;
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec_ref(v_msgData_3681_);
v_a_3690_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3687_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3687_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_3698_, lean_object* v_severity_3699_, lean_object* v_isSilent_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v_severity_boxed_3704_; uint8_t v_isSilent_boxed_3705_; lean_object* v_res_3706_; 
v_severity_boxed_3704_ = lean_unbox(v_severity_3699_);
v_isSilent_boxed_3705_ = lean_unbox(v_isSilent_3700_);
v_res_3706_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3698_, v_severity_boxed_3704_, v_isSilent_boxed_3705_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
uint8_t v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = 0;
v___x_3712_ = 0;
v___x_3713_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3707_, v___x_3711_, v___x_3712_, v___y_3708_, v___y_3709_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_3719_, lean_object* v_x_3720_){
_start:
{
if (lean_obj_tag(v_x_3720_) == 0)
{
lean_object* v_k_3722_; lean_object* v_v_3723_; lean_object* v_l_3724_; lean_object* v_r_3725_; lean_object* v___x_3726_; lean_object* v_a_3727_; lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_k_3722_ = lean_ctor_get(v_x_3720_, 1);
lean_inc(v_k_3722_);
v_v_3723_ = lean_ctor_get(v_x_3720_, 2);
lean_inc(v_v_3723_);
v_l_3724_ = lean_ctor_get(v_x_3720_, 3);
lean_inc(v_l_3724_);
v_r_3725_ = lean_ctor_get(v_x_3720_, 4);
lean_inc(v_r_3725_);
lean_dec_ref_known(v_x_3720_, 5);
v___x_3726_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3719_, v_l_3724_);
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref(v___x_3726_);
v_a_3728_ = lean_ctor_get(v_a_3727_, 0);
lean_inc(v_a_3728_);
lean_dec(v_a_3727_);
v___x_3729_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3722_, v_v_3723_, v_a_3728_);
v_init_3719_ = v___x_3729_;
v_x_3720_ = v_r_3725_;
goto _start;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_init_3719_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3733_, v_x_3734_);
return v_res_3736_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_3737_, lean_object* v_x1_3738_, lean_object* v_x2_3739_){
_start:
{
lean_object* v_fst_3740_; lean_object* v_fst_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v_fst_3740_ = lean_ctor_get(v_x1_3738_, 0);
lean_inc(v_fst_3740_);
lean_dec_ref(v_x1_3738_);
v_fst_3741_ = lean_ctor_get(v_x2_3739_, 0);
lean_inc(v_fst_3741_);
lean_dec_ref(v_x2_3739_);
v___x_3742_ = l_Lean_Name_toString(v_fst_3740_, v___x_3737_);
v___x_3743_ = l_Lean_Name_toString(v_fst_3741_, v___x_3737_);
v___x_3744_ = lean_string_dec_lt(v___x_3742_, v___x_3743_);
lean_dec_ref(v___x_3743_);
lean_dec_ref(v___x_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_3745_, lean_object* v_x1_3746_, lean_object* v_x2_3747_){
_start:
{
uint8_t v___x_18303__boxed_3748_; uint8_t v_res_3749_; lean_object* v_r_3750_; 
v___x_18303__boxed_3748_ = lean_unbox(v___x_3745_);
v_res_3749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18303__boxed_3748_, v_x1_3746_, v_x2_3747_);
v_r_3750_ = lean_box(v_res_3749_);
return v_r_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_3751_, lean_object* v_pivot_3752_, lean_object* v_as_3753_, lean_object* v_i_3754_, lean_object* v_k_3755_){
_start:
{
uint8_t v___x_3756_; 
v___x_3756_ = lean_nat_dec_lt(v_k_3755_, v_hi_3751_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_dec(v_k_3755_);
lean_dec_ref(v_pivot_3752_);
v___x_3757_ = lean_array_fswap(v_as_3753_, v_i_3754_, v_hi_3751_);
v___x_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3758_, 0, v_i_3754_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; lean_object* v_fst_3760_; lean_object* v_fst_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3759_ = lean_array_fget_borrowed(v_as_3753_, v_k_3755_);
v_fst_3760_ = lean_ctor_get(v___x_3759_, 0);
v_fst_3761_ = lean_ctor_get(v_pivot_3752_, 0);
lean_inc(v_fst_3760_);
v___x_3762_ = l_Lean_Name_toString(v_fst_3760_, v___x_3756_);
lean_inc(v_fst_3761_);
v___x_3763_ = l_Lean_Name_toString(v_fst_3761_, v___x_3756_);
v___x_3764_ = lean_string_dec_lt(v___x_3762_, v___x_3763_);
lean_dec_ref(v___x_3763_);
lean_dec_ref(v___x_3762_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = lean_unsigned_to_nat(1u);
v___x_3766_ = lean_nat_add(v_k_3755_, v___x_3765_);
lean_dec(v_k_3755_);
v_k_3755_ = v___x_3766_;
goto _start;
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3768_ = lean_array_fswap(v_as_3753_, v_i_3754_, v_k_3755_);
v___x_3769_ = lean_unsigned_to_nat(1u);
v___x_3770_ = lean_nat_add(v_i_3754_, v___x_3769_);
lean_dec(v_i_3754_);
v___x_3771_ = lean_nat_add(v_k_3755_, v___x_3769_);
lean_dec(v_k_3755_);
v_as_3753_ = v___x_3768_;
v_i_3754_ = v___x_3770_;
v_k_3755_ = v___x_3771_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_3773_, lean_object* v_pivot_3774_, lean_object* v_as_3775_, lean_object* v_i_3776_, lean_object* v_k_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3773_, v_pivot_3774_, v_as_3775_, v_i_3776_, v_k_3777_);
lean_dec(v_hi_3773_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_3779_, lean_object* v_as_3780_, lean_object* v_lo_3781_, lean_object* v_hi_3782_){
_start:
{
lean_object* v___y_3784_; uint8_t v___x_3794_; 
v___x_3794_ = lean_nat_dec_lt(v_lo_3781_, v_hi_3782_);
if (v___x_3794_ == 0)
{
lean_dec(v_lo_3781_);
return v_as_3780_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v_mid_3797_; lean_object* v___y_3799_; lean_object* v___y_3805_; lean_object* v___x_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
v___x_3795_ = lean_nat_add(v_lo_3781_, v_hi_3782_);
v___x_3796_ = lean_unsigned_to_nat(1u);
v_mid_3797_ = lean_nat_shiftr(v___x_3795_, v___x_3796_);
lean_dec(v___x_3795_);
v___x_3810_ = lean_array_fget_borrowed(v_as_3780_, v_mid_3797_);
v___x_3811_ = lean_array_fget_borrowed(v_as_3780_, v_lo_3781_);
lean_inc(v___x_3811_);
lean_inc(v___x_3810_);
v___x_3812_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3794_, v___x_3810_, v___x_3811_);
if (v___x_3812_ == 0)
{
v___y_3805_ = v_as_3780_;
goto v___jp_3804_;
}
else
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_array_fswap(v_as_3780_, v_lo_3781_, v_mid_3797_);
v___y_3805_ = v___x_3813_;
goto v___jp_3804_;
}
v___jp_3798_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3800_ = lean_array_fget_borrowed(v___y_3799_, v_mid_3797_);
v___x_3801_ = lean_array_fget_borrowed(v___y_3799_, v_hi_3782_);
lean_inc(v___x_3801_);
lean_inc(v___x_3800_);
v___x_3802_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3794_, v___x_3800_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_dec(v_mid_3797_);
v___y_3784_ = v___y_3799_;
goto v___jp_3783_;
}
else
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_array_fswap(v___y_3799_, v_mid_3797_, v_hi_3782_);
lean_dec(v_mid_3797_);
v___y_3784_ = v___x_3803_;
goto v___jp_3783_;
}
}
v___jp_3804_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3806_ = lean_array_fget_borrowed(v___y_3805_, v_hi_3782_);
v___x_3807_ = lean_array_fget_borrowed(v___y_3805_, v_lo_3781_);
lean_inc(v___x_3807_);
lean_inc(v___x_3806_);
v___x_3808_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3794_, v___x_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
v___y_3799_ = v___y_3805_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_array_fswap(v___y_3805_, v_lo_3781_, v_hi_3782_);
v___y_3799_ = v___x_3809_;
goto v___jp_3798_;
}
}
}
v___jp_3783_:
{
lean_object* v_pivot_3785_; lean_object* v___x_3786_; lean_object* v_fst_3787_; lean_object* v_snd_3788_; uint8_t v___x_3789_; 
v_pivot_3785_ = lean_array_fget(v___y_3784_, v_hi_3782_);
lean_inc_n(v_lo_3781_, 2);
v___x_3786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3782_, v_pivot_3785_, v___y_3784_, v_lo_3781_, v_lo_3781_);
v_fst_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_fst_3787_);
v_snd_3788_ = lean_ctor_get(v___x_3786_, 1);
lean_inc(v_snd_3788_);
lean_dec_ref(v___x_3786_);
v___x_3789_ = lean_nat_dec_le(v_hi_3782_, v_fst_3787_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3779_, v_snd_3788_, v_lo_3781_, v_fst_3787_);
v___x_3791_ = lean_unsigned_to_nat(1u);
v___x_3792_ = lean_nat_add(v_fst_3787_, v___x_3791_);
lean_dec(v_fst_3787_);
v_as_3780_ = v___x_3790_;
v_lo_3781_ = v___x_3792_;
goto _start;
}
else
{
lean_dec(v_fst_3787_);
lean_dec(v_lo_3781_);
return v_snd_3788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_3814_, lean_object* v_as_3815_, lean_object* v_lo_3816_, lean_object* v_hi_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3814_, v_as_3815_, v_lo_3816_, v_hi_3817_);
lean_dec(v_hi_3817_);
lean_dec(v_n_3814_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_3819_, lean_object* v_x_3820_){
_start:
{
if (lean_obj_tag(v_x_3820_) == 0)
{
lean_object* v_k_3821_; lean_object* v_v_3822_; lean_object* v_l_3823_; lean_object* v_r_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_k_3821_ = lean_ctor_get(v_x_3820_, 1);
v_v_3822_ = lean_ctor_get(v_x_3820_, 2);
v_l_3823_ = lean_ctor_get(v_x_3820_, 3);
v_r_3824_ = lean_ctor_get(v_x_3820_, 4);
v___x_3825_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3819_, v_l_3823_);
lean_inc(v_v_3822_);
lean_inc(v_k_3821_);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v_k_3821_);
lean_ctor_set(v___x_3826_, 1, v_v_3822_);
v___x_3827_ = lean_array_push(v___x_3825_, v___x_3826_);
v_init_3819_ = v___x_3827_;
v_x_3820_ = v_r_3824_;
goto _start;
}
else
{
return v_init_3819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_3829_, lean_object* v_x_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3829_, v_x_3830_);
lean_dec(v_x_3830_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_3832_, size_t v_sz_3833_, size_t v_i_3834_, lean_object* v_b_3835_){
_start:
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_usize_dec_lt(v_i_3834_, v_sz_3833_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v_b_3835_);
return v___x_3838_;
}
else
{
lean_object* v_a_3839_; lean_object* v_fst_3840_; lean_object* v_snd_3841_; lean_object* v_found_3842_; size_t v___x_3843_; size_t v___x_3844_; 
v_a_3839_ = lean_array_uget_borrowed(v_as_3832_, v_i_3834_);
v_fst_3840_ = lean_ctor_get(v_a_3839_, 0);
v_snd_3841_ = lean_ctor_get(v_a_3839_, 1);
lean_inc(v_snd_3841_);
lean_inc(v_fst_3840_);
v_found_3842_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3840_, v_snd_3841_, v_b_3835_);
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3834_, v___x_3843_);
v_i_3834_ = v___x_3844_;
v_b_3835_ = v_found_3842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_3846_, lean_object* v_sz_3847_, lean_object* v_i_3848_, lean_object* v_b_3849_, lean_object* v___y_3850_){
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3847_);
lean_dec(v_sz_3847_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3848_);
lean_dec(v_i_3848_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3846_, v_sz_boxed_3851_, v_i_boxed_3852_, v_b_3849_);
lean_dec_ref(v_as_3846_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3854_, size_t v_sz_3855_, size_t v_i_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
uint8_t v___x_3861_; 
v___x_3861_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_b_3857_);
return v___x_3862_;
}
else
{
lean_object* v_a_3863_; size_t v_sz_3864_; size_t v___x_3865_; lean_object* v___x_3866_; 
v_a_3863_ = lean_array_uget_borrowed(v_as_3854_, v_i_3856_);
v_sz_3864_ = lean_array_size(v_a_3863_);
v___x_3865_ = ((size_t)0ULL);
v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_3863_, v_sz_3864_, v___x_3865_, v_b_3857_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; size_t v___x_3868_; size_t v___x_3869_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v___x_3868_ = ((size_t)1ULL);
v___x_3869_ = lean_usize_add(v_i_3856_, v___x_3868_);
v_i_3856_ = v___x_3869_;
v_b_3857_ = v_a_3867_;
goto _start;
}
else
{
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3871_, lean_object* v_sz_3872_, lean_object* v_i_3873_, lean_object* v_b_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
size_t v_sz_boxed_3878_; size_t v_i_boxed_3879_; lean_object* v_res_3880_; 
v_sz_boxed_3878_ = lean_unbox_usize(v_sz_3872_);
lean_dec(v_sz_3872_);
v_i_boxed_3879_ = lean_unbox_usize(v_i_3873_);
lean_dec(v_i_3873_);
v_res_3880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3871_, v_sz_boxed_3878_, v_i_boxed_3879_, v_b_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v_as_3871_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___y_3887_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v_env_3905_; lean_object* v___x_3906_; lean_object* v_toEnvExtension_3907_; lean_object* v_asyncMode_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v_a_3912_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v_a_3937_; lean_object* v_a_3938_; 
v___x_3902_ = lean_box(1);
v___x_3903_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3904_ = lean_st_ref_get(v___y_3884_);
v_env_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc_ref_n(v_env_3905_, 2);
lean_dec(v___x_3904_);
v___x_3906_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_3907_ = lean_ctor_get(v___x_3906_, 0);
v_asyncMode_3908_ = lean_ctor_get(v_toEnvExtension_3907_, 2);
v___x_3909_ = lean_box(0);
v___x_3910_ = 0;
v___x_3935_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3902_, v___x_3906_, v_env_3905_, v_asyncMode_3908_, v___x_3909_, v___x_3910_);
v___x_3936_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_3902_, v___x_3935_);
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref(v___x_3936_);
v_a_3938_ = lean_ctor_get(v_a_3937_, 0);
lean_inc(v_a_3938_);
lean_dec(v_a_3937_);
v_a_3912_ = v_a_3938_;
goto v___jp_3911_;
v___jp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_array_to_list(v___y_3887_);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
v___jp_3890_:
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_3893_, v___y_3891_, v___y_3892_, v___y_3894_);
lean_dec(v___y_3894_);
lean_dec(v___y_3893_);
v___y_3887_ = v___x_3895_;
goto v___jp_3886_;
}
v___jp_3896_:
{
uint8_t v___x_3901_; 
v___x_3901_ = lean_nat_dec_le(v___y_3900_, v___y_3898_);
if (v___x_3901_ == 0)
{
lean_dec(v___y_3898_);
lean_inc(v___y_3900_);
v___y_3891_ = v___y_3897_;
v___y_3892_ = v___y_3900_;
v___y_3893_ = v___y_3899_;
v___y_3894_ = v___y_3900_;
goto v___jp_3890_;
}
else
{
v___y_3891_ = v___y_3897_;
v___y_3892_ = v___y_3900_;
v___y_3893_ = v___y_3899_;
v___y_3894_ = v___y_3898_;
goto v___jp_3890_;
}
}
v___jp_3911_:
{
lean_object* v___x_3913_; lean_object* v_importedEntries_3914_; size_t v_sz_3915_; size_t v___x_3916_; lean_object* v___x_3917_; 
v___x_3913_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3903_, v_toEnvExtension_3907_, v_env_3905_, v_asyncMode_3908_, v___x_3909_, v___x_3910_);
v_importedEntries_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc_ref(v_importedEntries_3914_);
lean_dec(v___x_3913_);
v_sz_3915_ = lean_array_size(v_importedEntries_3914_);
v___x_3916_ = ((size_t)0ULL);
v___x_3917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_3914_, v_sz_3915_, v___x_3916_, v_a_3912_, v___y_3883_, v___y_3884_);
lean_dec_ref(v_importedEntries_3914_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_arr_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = lean_unsigned_to_nat(0u);
v___x_3920_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_3921_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_3920_, v_a_3918_);
lean_dec(v_a_3918_);
v___x_3922_ = lean_array_get_size(v_arr_3921_);
v___x_3923_ = lean_nat_dec_eq(v___x_3922_, v___x_3919_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_nat_sub(v___x_3922_, v___x_3924_);
v___x_3926_ = lean_nat_dec_le(v___x_3919_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_inc(v___x_3925_);
v___y_3897_ = v_arr_3921_;
v___y_3898_ = v___x_3925_;
v___y_3899_ = v___x_3922_;
v___y_3900_ = v___x_3925_;
goto v___jp_3896_;
}
else
{
v___y_3897_ = v_arr_3921_;
v___y_3898_ = v___x_3925_;
v___y_3899_ = v___x_3922_;
v___y_3900_ = v___x_3919_;
goto v___jp_3896_;
}
}
else
{
v___y_3887_ = v_arr_3921_;
goto v___jp_3886_;
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
v_a_3927_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3917_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3917_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_3943_, lean_object* v_k_3944_, lean_object* v_fallback_3945_){
_start:
{
if (lean_obj_tag(v_t_3943_) == 0)
{
lean_object* v_k_3946_; lean_object* v_v_3947_; lean_object* v_l_3948_; lean_object* v_r_3949_; uint8_t v___x_3950_; 
v_k_3946_ = lean_ctor_get(v_t_3943_, 1);
v_v_3947_ = lean_ctor_get(v_t_3943_, 2);
v_l_3948_ = lean_ctor_get(v_t_3943_, 3);
v_r_3949_ = lean_ctor_get(v_t_3943_, 4);
v___x_3950_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3944_, v_k_3946_);
switch(v___x_3950_)
{
case 0:
{
v_t_3943_ = v_l_3948_;
goto _start;
}
case 1:
{
lean_inc(v_v_3947_);
return v_v_3947_;
}
default: 
{
v_t_3943_ = v_r_3949_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3945_);
return v_fallback_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_3953_, lean_object* v_k_3954_, lean_object* v_fallback_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3953_, v_k_3954_, v_fallback_3955_);
lean_dec(v_fallback_3955_);
lean_dec(v_k_3954_);
lean_dec(v_t_3953_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_3957_, size_t v_sz_3958_, size_t v_i_3959_, lean_object* v_b_3960_){
_start:
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_usize_dec_lt(v_i_3959_, v_sz_3958_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v_b_3960_);
return v___x_3963_;
}
else
{
lean_object* v_a_3964_; lean_object* v_fst_3965_; lean_object* v_snd_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; size_t v___x_3971_; size_t v___x_3972_; 
v_a_3964_ = lean_array_uget_borrowed(v_as_3957_, v_i_3959_);
v_fst_3965_ = lean_ctor_get(v_a_3964_, 0);
v_snd_3966_ = lean_ctor_get(v_a_3964_, 1);
v___x_3967_ = l_Lean_NameSet_empty;
v___x_3968_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3960_, v_snd_3966_, v___x_3967_);
lean_inc(v_fst_3965_);
v___x_3969_ = l_Lean_NameSet_insert(v___x_3968_, v_fst_3965_);
lean_inc(v_snd_3966_);
v___x_3970_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_3966_, v___x_3969_, v_b_3960_);
v___x_3971_ = ((size_t)1ULL);
v___x_3972_ = lean_usize_add(v_i_3959_, v___x_3971_);
v_i_3959_ = v___x_3972_;
v_b_3960_ = v___x_3970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_3974_, lean_object* v_sz_3975_, lean_object* v_i_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_){
_start:
{
size_t v_sz_boxed_3979_; size_t v_i_boxed_3980_; lean_object* v_res_3981_; 
v_sz_boxed_3979_ = lean_unbox_usize(v_sz_3975_);
lean_dec(v_sz_3975_);
v_i_boxed_3980_ = lean_unbox_usize(v_i_3976_);
lean_dec(v_i_3976_);
v_res_3981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3974_, v_sz_boxed_3979_, v_i_boxed_3980_, v_b_3977_);
lean_dec_ref(v_as_3974_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_3982_, size_t v_sz_3983_, size_t v_i_3984_, lean_object* v_b_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
uint8_t v___x_3989_; 
v___x_3989_ = lean_usize_dec_lt(v_i_3984_, v_sz_3983_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_b_3985_);
return v___x_3990_;
}
else
{
lean_object* v_a_3991_; size_t v_sz_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v_a_3991_ = lean_array_uget_borrowed(v_as_3982_, v_i_3984_);
v_sz_3992_ = lean_array_size(v_a_3991_);
v___x_3993_ = ((size_t)0ULL);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_3991_, v_sz_3992_, v___x_3993_, v_b_3985_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; size_t v___x_3996_; size_t v___x_3997_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3994_, 1);
v___x_3996_ = ((size_t)1ULL);
v___x_3997_ = lean_usize_add(v_i_3984_, v___x_3996_);
v_i_3984_ = v___x_3997_;
v_b_3985_ = v_a_3995_;
goto _start;
}
else
{
return v___x_3994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_3999_, lean_object* v_sz_4000_, lean_object* v_i_4001_, lean_object* v_b_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
size_t v_sz_boxed_4006_; size_t v_i_boxed_4007_; lean_object* v_res_4008_; 
v_sz_boxed_4006_ = lean_unbox_usize(v_sz_4000_);
lean_dec(v_sz_4000_);
v_i_boxed_4007_ = lean_unbox_usize(v_i_4001_);
lean_dec(v_i_4001_);
v_res_4008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_3999_, v_sz_boxed_4006_, v_i_boxed_4007_, v_b_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec_ref(v_as_3999_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_4009_, size_t v_i_4010_, size_t v_stop_4011_, lean_object* v_b_4012_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_usize_dec_eq(v_i_4010_, v_stop_4011_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v_fst_4015_; lean_object* v_snd_4016_; lean_object* v___x_4017_; size_t v___x_4018_; size_t v___x_4019_; 
v___x_4014_ = lean_array_uget_borrowed(v_as_4009_, v_i_4010_);
v_fst_4015_ = lean_ctor_get(v___x_4014_, 0);
v_snd_4016_ = lean_ctor_get(v___x_4014_, 1);
lean_inc(v_snd_4016_);
lean_inc(v_fst_4015_);
v___x_4017_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4015_, v_snd_4016_, v_b_4012_);
v___x_4018_ = ((size_t)1ULL);
v___x_4019_ = lean_usize_add(v_i_4010_, v___x_4018_);
v_i_4010_ = v___x_4019_;
v_b_4012_ = v___x_4017_;
goto _start;
}
else
{
return v_b_4012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_4021_, lean_object* v_i_4022_, lean_object* v_stop_4023_, lean_object* v_b_4024_){
_start:
{
size_t v_i_boxed_4025_; size_t v_stop_boxed_4026_; lean_object* v_res_4027_; 
v_i_boxed_4025_ = lean_unbox_usize(v_i_4022_);
lean_dec(v_i_4022_);
v_stop_boxed_4026_ = lean_unbox_usize(v_stop_4023_);
lean_dec(v_stop_4023_);
v_res_4027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_4021_, v_i_boxed_4025_, v_stop_boxed_4026_, v_b_4024_);
lean_dec_ref(v_as_4021_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_4028_, size_t v_i_4029_, size_t v_stop_4030_, lean_object* v_b_4031_){
_start:
{
lean_object* v___y_4033_; uint8_t v___x_4037_; 
v___x_4037_ = lean_usize_dec_eq(v_i_4029_, v_stop_4030_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4038_ = lean_array_uget_borrowed(v_as_4028_, v_i_4029_);
v___x_4039_ = lean_unsigned_to_nat(0u);
v___x_4040_ = lean_array_get_size(v___x_4038_);
v___x_4041_ = lean_nat_dec_lt(v___x_4039_, v___x_4040_);
if (v___x_4041_ == 0)
{
v___y_4033_ = v_b_4031_;
goto v___jp_4032_;
}
else
{
size_t v___x_4042_; size_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = ((size_t)0ULL);
v___x_4043_ = lean_usize_of_nat(v___x_4040_);
v___x_4044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_4038_, v___x_4042_, v___x_4043_, v_b_4031_);
v___y_4033_ = v___x_4044_;
goto v___jp_4032_;
}
}
else
{
return v_b_4031_;
}
v___jp_4032_:
{
size_t v___x_4034_; size_t v___x_4035_; 
v___x_4034_ = ((size_t)1ULL);
v___x_4035_ = lean_usize_add(v_i_4029_, v___x_4034_);
v_i_4029_ = v___x_4035_;
v_b_4031_ = v___y_4033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_4045_, lean_object* v_i_4046_, lean_object* v_stop_4047_, lean_object* v_b_4048_){
_start:
{
size_t v_i_boxed_4049_; size_t v_stop_boxed_4050_; lean_object* v_res_4051_; 
v_i_boxed_4049_ = lean_unbox_usize(v_i_4046_);
lean_dec(v_i_4046_);
v_stop_boxed_4050_ = lean_unbox_usize(v_stop_4047_);
lean_dec(v_stop_4047_);
v_res_4051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_4045_, v_i_boxed_4049_, v_stop_boxed_4050_, v_b_4048_);
lean_dec_ref(v_as_4045_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v_env_4058_; lean_object* v___x_4059_; lean_object* v_ext_4060_; lean_object* v_toEnvExtension_4061_; lean_object* v_asyncMode_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; lean_object* v_categories_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4054_ = lean_box(1);
v___x_4055_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4056_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4057_ = lean_st_ref_get(v___y_4052_);
v_env_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc_ref_n(v_env_4058_, 2);
lean_dec(v___x_4057_);
v___x_4059_ = l_Lean_Parser_parserExtension;
v_ext_4060_ = lean_ctor_get(v___x_4059_, 1);
v_toEnvExtension_4061_ = lean_ctor_get(v_ext_4060_, 0);
v_asyncMode_4062_ = lean_ctor_get(v_toEnvExtension_4061_, 2);
v___x_4063_ = 0;
v___x_4064_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4056_, v___x_4059_, v_env_4058_, v_asyncMode_4062_, v___x_4063_);
v_categories_4065_ = lean_ctor_get(v___x_4064_, 2);
lean_inc_ref(v_categories_4065_);
lean_dec(v___x_4064_);
v___x_4066_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4067_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4065_, v___x_4066_);
lean_dec_ref(v_categories_4065_);
if (lean_obj_tag(v___x_4067_) == 1)
{
lean_object* v_val_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4099_; 
v_val_4068_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4099_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_val_4068_);
lean_dec(v___x_4067_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4099_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___y_4073_; lean_object* v___x_4082_; lean_object* v_toEnvExtension_4083_; lean_object* v_exportEntriesFn_4084_; lean_object* v_asyncMode_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v_importedEntries_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v_exported_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4082_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4083_ = lean_ctor_get(v___x_4082_, 0);
v_exportEntriesFn_4084_ = lean_ctor_get(v___x_4082_, 4);
v_asyncMode_4085_ = lean_ctor_get(v_toEnvExtension_4083_, 2);
v___x_4086_ = lean_box(0);
lean_inc_ref_n(v_env_4058_, 2);
v___x_4087_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4055_, v_toEnvExtension_4083_, v_env_4058_, v_asyncMode_4085_, v___x_4086_, v___x_4063_);
v_importedEntries_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc_ref(v_importedEntries_4088_);
lean_dec(v___x_4087_);
v___x_4089_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4054_, v___x_4082_, v_env_4058_, v_asyncMode_4085_, v___x_4086_, v___x_4063_);
lean_inc_ref(v_exportEntriesFn_4084_);
v___x_4090_ = lean_apply_2(v_exportEntriesFn_4084_, v_env_4058_, v___x_4089_);
v_exported_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_exported_4091_);
lean_dec_ref(v___x_4090_);
v___x_4092_ = lean_array_push(v_importedEntries_4088_, v_exported_4091_);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = lean_array_get_size(v___x_4092_);
v___x_4095_ = lean_nat_dec_lt(v___x_4093_, v___x_4094_);
if (v___x_4095_ == 0)
{
lean_dec_ref(v___x_4092_);
v___y_4073_ = v___x_4054_;
goto v___jp_4072_;
}
else
{
size_t v___x_4096_; size_t v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = ((size_t)0ULL);
v___x_4097_ = lean_usize_of_nat(v___x_4094_);
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4092_, v___x_4096_, v___x_4097_, v___x_4054_);
lean_dec_ref(v___x_4092_);
v___y_4073_ = v___x_4098_;
goto v___jp_4072_;
}
v___jp_4072_:
{
lean_object* v_tables_4074_; lean_object* v_leadingTable_4075_; lean_object* v_trailingTable_4076_; lean_object* v_firstTokens_4077_; lean_object* v_firstTokens_4078_; lean_object* v___x_4080_; 
v_tables_4074_ = lean_ctor_get(v_val_4068_, 2);
v_leadingTable_4075_ = lean_ctor_get(v_tables_4074_, 0);
v_trailingTable_4076_ = lean_ctor_get(v_tables_4074_, 2);
lean_inc(v_trailingTable_4076_);
lean_inc(v_leadingTable_4075_);
lean_inc(v_val_4068_);
v_firstTokens_4077_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4068_, v_leadingTable_4075_, v___y_4073_);
v_firstTokens_4078_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4068_, v_trailingTable_4076_, v_firstTokens_4077_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set_tag(v___x_4070_, 0);
lean_ctor_set(v___x_4070_, 0, v_firstTokens_4078_);
v___x_4080_ = v___x_4070_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_firstTokens_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
else
{
lean_object* v___x_4100_; 
lean_dec(v___x_4067_);
lean_dec_ref(v_env_4058_);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4054_);
return v___x_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4101_);
lean_dec(v___y_4101_);
return v_res_4103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_4106_ = l_Lean_stringToMessageData(v___x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v_env_4113_; lean_object* v___x_4114_; lean_object* v_env_4115_; lean_object* v___x_4116_; lean_object* v_env_4117_; lean_object* v___x_4118_; lean_object* v_toEnvExtension_4119_; lean_object* v_exportEntriesFn_4120_; lean_object* v_asyncMode_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v_importedEntries_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4177_; 
v___x_4110_ = lean_box(1);
v___x_4111_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4112_ = lean_st_ref_get(v_a_4108_);
v_env_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc_ref(v_env_4113_);
lean_dec(v___x_4112_);
v___x_4114_ = lean_st_ref_get(v_a_4108_);
v_env_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc_ref(v_env_4115_);
lean_dec(v___x_4114_);
v___x_4116_ = lean_st_ref_get(v_a_4108_);
v_env_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc_ref(v_env_4117_);
lean_dec(v___x_4116_);
v___x_4118_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4119_ = lean_ctor_get(v___x_4118_, 0);
v_exportEntriesFn_4120_ = lean_ctor_get(v___x_4118_, 4);
v_asyncMode_4121_ = lean_ctor_get(v_toEnvExtension_4119_, 2);
v___x_4122_ = lean_box(0);
v___x_4123_ = 0;
v___x_4124_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4111_, v_toEnvExtension_4119_, v_env_4113_, v_asyncMode_4121_, v___x_4122_, v___x_4123_);
v_importedEntries_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4177_ == 0)
{
lean_object* v_unused_4178_; 
v_unused_4178_ = lean_ctor_get(v___x_4124_, 1);
lean_dec(v_unused_4178_);
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4177_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_importedEntries_4125_);
lean_dec(v___x_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4177_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v_exported_4131_; lean_object* v___x_4132_; size_t v_sz_4133_; size_t v___x_4134_; lean_object* v___x_4135_; 
v___x_4129_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4110_, v___x_4118_, v_env_4117_, v_asyncMode_4121_, v___x_4122_, v___x_4123_);
lean_inc_ref(v_exportEntriesFn_4120_);
v___x_4130_ = lean_apply_2(v_exportEntriesFn_4120_, v_env_4115_, v___x_4129_);
v_exported_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_exported_4131_);
lean_dec_ref(v___x_4130_);
v___x_4132_ = lean_array_push(v_importedEntries_4125_, v_exported_4131_);
v_sz_4133_ = lean_array_size(v___x_4132_);
v___x_4134_ = ((size_t)0ULL);
v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_4132_, v_sz_4133_, v___x_4134_, v___x_4110_, v_a_4107_, v_a_4108_);
lean_dec_ref(v___x_4132_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4137_; lean_object* v_a_4138_; lean_object* v___x_4139_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_4108_);
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref(v___x_4137_);
v___x_4139_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_4107_, v_a_4108_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___x_4141_ = lean_box(0);
v___x_4142_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_4138_, v_a_4136_, v_a_4140_, v___x_4141_, v_a_4107_, v_a_4108_);
lean_dec(v_a_4136_);
lean_dec(v_a_4138_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_4145_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_4146_ = l_Lean_MessageData_joinSep(v_a_4143_, v___x_4145_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 7);
lean_ctor_set(v___x_4127_, 1, v___x_4146_);
lean_ctor_set(v___x_4127_, 0, v___x_4145_);
v___x_4148_ = v___x_4127_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4152_, 1, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = l_Lean_MessageData_nestD(v___x_4148_);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4144_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_4150_, v_a_4107_, v_a_4108_);
return v___x_4151_;
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_del_object(v___x_4127_);
v_a_4153_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4142_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4142_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec(v_a_4138_);
lean_dec(v_a_4136_);
lean_del_object(v___x_4127_);
v_a_4161_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4139_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4139_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_del_object(v___x_4127_);
v_a_4169_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4135_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4135_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4184_, v_a_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4188_, v_a_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v___stx_4188_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_4193_, lean_object* v_t_4194_, lean_object* v_k_4195_, lean_object* v_fallback_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4194_, v_k_4195_, v_fallback_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_4198_, lean_object* v_t_4199_, lean_object* v_k_4200_, lean_object* v_fallback_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_4198_, v_t_4199_, v_k_4200_, v_fallback_4201_);
lean_dec(v_fallback_4201_);
lean_dec(v_k_4200_);
lean_dec(v_t_4199_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_4203_, size_t v_sz_4204_, size_t v_i_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4203_, v_sz_4204_, v_i_4205_, v_b_4206_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_4211_, lean_object* v_sz_4212_, lean_object* v_i_4213_, lean_object* v_b_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
size_t v_sz_boxed_4218_; size_t v_i_boxed_4219_; lean_object* v_res_4220_; 
v_sz_boxed_4218_ = lean_unbox_usize(v_sz_4212_);
lean_dec(v_sz_4212_);
v_i_boxed_4219_ = lean_unbox_usize(v_i_4213_);
lean_dec(v_i_4213_);
v_res_4220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4211_, v_sz_boxed_4218_, v_i_boxed_4219_, v_b_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec_ref(v_as_4211_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4222_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_4229_, lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v_inst_4232_, lean_object* v_R_4233_, lean_object* v_a_4234_, lean_object* v_b_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_4229_, v___x_4230_, v___x_4231_, v_a_4234_, v_b_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_4237_, lean_object* v___x_4238_, lean_object* v___x_4239_, lean_object* v_inst_4240_, lean_object* v_R_4241_, lean_object* v_a_4242_, lean_object* v_b_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_4237_, v___x_4238_, v___x_4239_, v_inst_4240_, v_R_4241_, v_a_4242_, v_b_4243_);
lean_dec_ref(v___x_4238_);
lean_dec_ref(v_val_4237_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_4245_, lean_object* v_t_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_4245_, v_t_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_4248_, lean_object* v_as_4249_, lean_object* v_lo_4250_, lean_object* v_hi_4251_, lean_object* v_w_4252_, lean_object* v_hlo_4253_, lean_object* v_hhi_4254_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_4248_, v_as_4249_, v_lo_4250_, v_hi_4251_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_4256_, lean_object* v_as_4257_, lean_object* v_lo_4258_, lean_object* v_hi_4259_, lean_object* v_w_4260_, lean_object* v_hlo_4261_, lean_object* v_hhi_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_4256_, v_as_4257_, v_lo_4258_, v_hi_4259_, v_w_4260_, v_hlo_4261_, v_hhi_4262_);
lean_dec(v_hi_4259_);
lean_dec(v_n_4256_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_4264_, lean_object* v_x_4265_, lean_object* v_x_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_4265_, v_x_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4268_, lean_object* v_x_4269_, lean_object* v_x_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_4268_, v_x_4269_, v_x_4270_);
lean_dec(v_x_4270_);
lean_dec_ref(v_x_4269_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_4272_, v___y_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_4282_, lean_object* v_t_4283_, lean_object* v_k_4284_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_4283_, v_k_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_4286_, lean_object* v_t_4287_, lean_object* v_k_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_4286_, v_t_4287_, v_k_4288_);
lean_dec(v_k_4288_);
lean_dec(v_t_4287_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_4290_, lean_object* v_x_4291_, lean_object* v_x_4292_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_4291_, v_x_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_4294_, lean_object* v_x_4295_, lean_object* v_x_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_4294_, v_x_4295_, v_x_4296_);
lean_dec(v_x_4296_);
lean_dec_ref(v_x_4295_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_4298_, lean_object* v_lo_4299_, lean_object* v_hi_4300_, lean_object* v_hhi_4301_, lean_object* v_pivot_4302_, lean_object* v_as_4303_, lean_object* v_i_4304_, lean_object* v_k_4305_, lean_object* v_ilo_4306_, lean_object* v_ik_4307_, lean_object* v_w_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_4300_, v_pivot_4302_, v_as_4303_, v_i_4304_, v_k_4305_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_4310_, lean_object* v_lo_4311_, lean_object* v_hi_4312_, lean_object* v_hhi_4313_, lean_object* v_pivot_4314_, lean_object* v_as_4315_, lean_object* v_i_4316_, lean_object* v_k_4317_, lean_object* v_ilo_4318_, lean_object* v_ik_4319_, lean_object* v_w_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_4310_, v_lo_4311_, v_hi_4312_, v_hhi_4313_, v_pivot_4314_, v_as_4315_, v_i_4316_, v_k_4317_, v_ilo_4318_, v_ik_4319_, v_w_4320_);
lean_dec(v_hi_4312_);
lean_dec(v_lo_4311_);
lean_dec(v_n_4310_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_4322_, size_t v_sz_4323_, size_t v_i_4324_, lean_object* v_b_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4322_, v_sz_4323_, v_i_4324_, v_b_4325_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_4330_, lean_object* v_sz_4331_, lean_object* v_i_4332_, lean_object* v_b_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
size_t v_sz_boxed_4337_; size_t v_i_boxed_4338_; lean_object* v_res_4339_; 
v_sz_boxed_4337_ = lean_unbox_usize(v_sz_4331_);
lean_dec(v_sz_4331_);
v_i_boxed_4338_ = lean_unbox_usize(v_i_4332_);
lean_dec(v_i_4332_);
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4330_, v_sz_boxed_4337_, v_i_boxed_4338_, v_b_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec_ref(v_as_4330_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_4340_, lean_object* v_t_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4340_, v_t_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_4343_, lean_object* v_t_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_4343_, v_t_4344_);
lean_dec(v_t_4344_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_4346_, lean_object* v_as_4347_, lean_object* v_lo_4348_, lean_object* v_hi_4349_, lean_object* v_w_4350_, lean_object* v_hlo_4351_, lean_object* v_hhi_4352_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4346_, v_as_4347_, v_lo_4348_, v_hi_4349_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_4354_, lean_object* v_as_4355_, lean_object* v_lo_4356_, lean_object* v_hi_4357_, lean_object* v_w_4358_, lean_object* v_hlo_4359_, lean_object* v_hhi_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_4354_, v_as_4355_, v_lo_4356_, v_hi_4357_, v_w_4358_, v_hlo_4359_, v_hhi_4360_);
lean_dec(v_hi_4357_);
lean_dec(v_n_4354_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_4362_, lean_object* v_x_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4362_, v_x_4363_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_4368_, lean_object* v_x_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4368_, v_x_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_4374_, lean_object* v_x_4375_, size_t v_x_4376_, lean_object* v_x_4377_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_4375_, v_x_4376_, v_x_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4379_, lean_object* v_x_4380_, lean_object* v_x_4381_, lean_object* v_x_4382_){
_start:
{
size_t v_x_19011__boxed_4383_; lean_object* v_res_4384_; 
v_x_19011__boxed_4383_ = lean_unbox_usize(v_x_4381_);
lean_dec(v_x_4381_);
v_res_4384_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_4379_, v_x_4380_, v_x_19011__boxed_4383_, v_x_4382_);
lean_dec(v_x_4382_);
lean_dec_ref(v_x_4380_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_4385_, lean_object* v_k_4386_, lean_object* v_x_4387_, lean_object* v_x_4388_, lean_object* v_x_4389_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_4385_, v_k_4386_, v_x_4387_, v_x_4388_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_4391_, lean_object* v_k_4392_, lean_object* v_x_4393_, lean_object* v_x_4394_, lean_object* v_x_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_4391_, v_k_4392_, v_x_4393_, v_x_4394_, v_x_4395_);
lean_dec_ref(v_k_4392_);
lean_dec_ref(v_as_4391_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_4397_, lean_object* v_m_4398_, lean_object* v_a_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_4398_, v_a_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_4401_, lean_object* v_m_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_4401_, v_m_4402_, v_a_4403_);
lean_dec(v_a_4403_);
lean_dec_ref(v_m_4402_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_4405_, lean_object* v_lo_4406_, lean_object* v_hi_4407_, lean_object* v_hhi_4408_, lean_object* v_pivot_4409_, lean_object* v_as_4410_, lean_object* v_i_4411_, lean_object* v_k_4412_, lean_object* v_ilo_4413_, lean_object* v_ik_4414_, lean_object* v_w_4415_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4407_, v_pivot_4409_, v_as_4410_, v_i_4411_, v_k_4412_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_4417_, lean_object* v_lo_4418_, lean_object* v_hi_4419_, lean_object* v_hhi_4420_, lean_object* v_pivot_4421_, lean_object* v_as_4422_, lean_object* v_i_4423_, lean_object* v_k_4424_, lean_object* v_ilo_4425_, lean_object* v_ik_4426_, lean_object* v_w_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_4417_, v_lo_4418_, v_hi_4419_, v_hhi_4420_, v_pivot_4421_, v_as_4422_, v_i_4423_, v_k_4424_, v_ilo_4425_, v_ik_4426_, v_w_4427_);
lean_dec(v_hi_4419_);
lean_dec(v_lo_4418_);
lean_dec(v_n_4417_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_4429_, lean_object* v_keys_4430_, lean_object* v_vals_4431_, lean_object* v_heq_4432_, lean_object* v_i_4433_, lean_object* v_k_4434_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_4430_, v_vals_4431_, v_i_4433_, v_k_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_4436_, lean_object* v_keys_4437_, lean_object* v_vals_4438_, lean_object* v_heq_4439_, lean_object* v_i_4440_, lean_object* v_k_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_4436_, v_keys_4437_, v_vals_4438_, v_heq_4439_, v_i_4440_, v_k_4441_);
lean_dec(v_k_4441_);
lean_dec_ref(v_vals_4438_);
lean_dec_ref(v_keys_4437_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_4443_, lean_object* v_a_4444_, lean_object* v_x_4445_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_4444_, v_x_4445_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_4447_, lean_object* v_a_4448_, lean_object* v_x_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_4447_, v_a_4448_, v_x_4449_);
lean_dec(v_x_4449_);
lean_dec(v_a_4448_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4465_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4468_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_4469_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4465_, v___x_4466_, v___x_4467_, v___x_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_4476_ = l_Lean_addBuiltinDocString(v___x_4474_, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_4507_ = l_Lean_addBuiltinDeclarationRanges(v___x_4505_, v___x_4506_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_4510_, lean_object* v___x_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, uint8_t v_includeUnnamed_4514_, lean_object* v_x_4515_, lean_object* v_____s_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_fst_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4577_; 
v_fst_4522_ = lean_ctor_get(v_x_4515_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_x_4515_);
if (v_isSharedCheck_4577_ == 0)
{
lean_object* v_unused_4578_; 
v_unused_4578_ = lean_ctor_get(v_x_4515_, 1);
lean_dec(v_unused_4578_);
v___x_4524_ = v_x_4515_;
v_isShared_4525_ = v_isSharedCheck_4577_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_fst_4522_);
lean_dec(v_x_4515_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4577_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v_userName_4527_; lean_object* v___y_4528_; lean_object* v___x_4562_; 
lean_inc(v_fst_4522_);
lean_inc_ref(v_env_4510_);
v___x_4562_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4510_, v_fst_4522_);
if (lean_obj_tag(v___x_4562_) == 1)
{
lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
lean_del_object(v___x_4524_);
lean_dec(v_fst_4522_);
lean_dec(v___x_4511_);
lean_dec_ref(v_env_4510_);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4570_ == 0)
{
lean_object* v_unused_4571_; 
v_unused_4571_ = lean_ctor_get(v___x_4562_, 0);
lean_dec(v_unused_4571_);
v___x_4564_ = v___x_4562_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_dec(v___x_4562_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v_____s_4516_);
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_____s_4516_);
v___x_4567_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4568_; 
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
}
}
else
{
lean_object* v___x_4572_; 
lean_dec(v___x_4562_);
v___x_4572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_4513_, v_fst_4522_);
if (lean_obj_tag(v___x_4572_) == 1)
{
lean_object* v_val_4573_; 
v_val_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v_userName_4527_ = v_val_4573_;
v___y_4528_ = v___y_4519_;
goto v___jp_4526_;
}
else
{
lean_dec(v___x_4572_);
if (v_includeUnnamed_4514_ == 0)
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_del_object(v___x_4524_);
lean_dec(v_fst_4522_);
lean_dec(v___x_4511_);
lean_dec_ref(v_env_4510_);
v___x_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4574_, 0, v_____s_4516_);
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
return v___x_4575_;
}
else
{
lean_object* v___x_4576_; 
lean_inc(v_fst_4522_);
v___x_4576_ = l_Lean_Name_toString(v_fst_4522_, v_includeUnnamed_4514_);
v_userName_4527_ = v___x_4576_;
v___y_4528_ = v___y_4519_;
goto v___jp_4526_;
}
}
}
v___jp_4526_:
{
lean_object* v_ref_4529_; uint8_t v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v_ref_4529_ = lean_ctor_get(v___y_4528_, 2);
v___x_4530_ = 1;
v___x_4531_ = l_Lean_Options_empty;
v___x_4532_ = lean_box(0);
lean_inc(v_fst_4522_);
lean_inc_ref(v_env_4510_);
v___x_4533_ = l_Lean_findDocString_x3f(v_env_4510_, v_fst_4522_, v___x_4530_, v___x_4531_, v___x_4511_, v___x_4532_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4547_; 
lean_del_object(v___x_4524_);
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4547_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4547_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4545_; 
v___x_4538_ = l_Lean_NameSet_empty;
v___x_4539_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_4512_, v_fst_4522_, v___x_4538_);
lean_inc(v_fst_4522_);
v___x_4540_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_4510_, v_fst_4522_);
v___x_4541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4541_, 0, v_fst_4522_);
lean_ctor_set(v___x_4541_, 1, v_userName_4527_);
lean_ctor_set(v___x_4541_, 2, v___x_4539_);
lean_ctor_set(v___x_4541_, 3, v_a_4534_);
lean_ctor_set(v___x_4541_, 4, v___x_4540_);
v___x_4542_ = lean_array_push(v_____s_4516_, v___x_4541_);
v___x_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4543_);
v___x_4545_ = v___x_4536_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4543_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v_userName_4527_);
lean_dec(v_fst_4522_);
lean_dec_ref(v_____s_4516_);
lean_dec_ref(v_env_4510_);
v_a_4548_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4550_ = v___x_4533_;
v_isShared_4551_ = v_isSharedCheck_4561_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4533_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4561_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4552_ = lean_io_error_to_string(v_a_4548_);
v___x_4553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
v___x_4554_ = l_Lean_MessageData_ofFormat(v___x_4553_);
lean_inc(v_ref_4529_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 1, v___x_4554_);
lean_ctor_set(v___x_4524_, 0, v_ref_4529_);
v___x_4556_ = v___x_4524_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_ref_4529_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4558_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4556_);
v___x_4558_ = v___x_4550_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_4579_, lean_object* v___x_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_includeUnnamed_4583_, lean_object* v_x_4584_, lean_object* v_____s_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
uint8_t v_includeUnnamed_boxed_4591_; lean_object* v_res_4592_; 
v_includeUnnamed_boxed_4591_ = lean_unbox(v_includeUnnamed_4583_);
v_res_4592_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4579_, v___x_4580_, v_a_4581_, v_a_4582_, v_includeUnnamed_boxed_4591_, v_x_4584_, v_____s_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v_a_4582_);
lean_dec(v_a_4581_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_4593_, size_t v_sz_4594_, size_t v_i_4595_, lean_object* v_b_4596_){
_start:
{
uint8_t v___x_4598_; 
v___x_4598_ = lean_usize_dec_lt(v_i_4595_, v_sz_4594_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v_b_4596_);
return v___x_4599_;
}
else
{
lean_object* v_a_4600_; lean_object* v_fst_4601_; lean_object* v_snd_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; size_t v___x_4607_; size_t v___x_4608_; 
v_a_4600_ = lean_array_uget_borrowed(v_as_4593_, v_i_4595_);
v_fst_4601_ = lean_ctor_get(v_a_4600_, 0);
v_snd_4602_ = lean_ctor_get(v_a_4600_, 1);
v___x_4603_ = l_Lean_NameSet_empty;
v___x_4604_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4596_, v_fst_4601_, v___x_4603_);
lean_inc(v_snd_4602_);
v___x_4605_ = l_Lean_NameSet_insert(v___x_4604_, v_snd_4602_);
lean_inc(v_fst_4601_);
v___x_4606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4601_, v___x_4605_, v_b_4596_);
v___x_4607_ = ((size_t)1ULL);
v___x_4608_ = lean_usize_add(v_i_4595_, v___x_4607_);
v_i_4595_ = v___x_4608_;
v_b_4596_ = v___x_4606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_4610_, lean_object* v_sz_4611_, lean_object* v_i_4612_, lean_object* v_b_4613_, lean_object* v___y_4614_){
_start:
{
size_t v_sz_boxed_4615_; size_t v_i_boxed_4616_; lean_object* v_res_4617_; 
v_sz_boxed_4615_ = lean_unbox_usize(v_sz_4611_);
lean_dec(v_sz_4611_);
v_i_boxed_4616_ = lean_unbox_usize(v_i_4612_);
lean_dec(v_i_4612_);
v_res_4617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4610_, v_sz_boxed_4615_, v_i_boxed_4616_, v_b_4613_);
lean_dec_ref(v_as_4610_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_4618_, size_t v_sz_4619_, size_t v_i_4620_, lean_object* v_b_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
uint8_t v___x_4627_; 
v___x_4627_ = lean_usize_dec_lt(v_i_4620_, v_sz_4619_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; 
v___x_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4628_, 0, v_b_4621_);
return v___x_4628_;
}
else
{
lean_object* v_a_4629_; size_t v_sz_4630_; size_t v___x_4631_; lean_object* v___x_4632_; 
v_a_4629_ = lean_array_uget_borrowed(v_as_4618_, v_i_4620_);
v_sz_4630_ = lean_array_size(v_a_4629_);
v___x_4631_ = ((size_t)0ULL);
v___x_4632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_4629_, v_sz_4630_, v___x_4631_, v_b_4621_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; size_t v___x_4634_; size_t v___x_4635_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
v___x_4634_ = ((size_t)1ULL);
v___x_4635_ = lean_usize_add(v_i_4620_, v___x_4634_);
v_i_4620_ = v___x_4635_;
v_b_4621_ = v_a_4633_;
goto _start;
}
else
{
return v___x_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_4637_, lean_object* v_sz_4638_, lean_object* v_i_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
size_t v_sz_boxed_4646_; size_t v_i_boxed_4647_; lean_object* v_res_4648_; 
v_sz_boxed_4646_ = lean_unbox_usize(v_sz_4638_);
lean_dec(v_sz_4638_);
v_i_boxed_4647_ = lean_unbox_usize(v_i_4639_);
lean_dec(v_i_4639_);
v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4637_, v_sz_boxed_4646_, v_i_boxed_4647_, v_b_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec_ref(v_as_4637_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_4649_, lean_object* v_keys_4650_, lean_object* v_vals_4651_, lean_object* v_i_4652_, lean_object* v_acc_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; uint8_t v___x_4660_; 
v___x_4659_ = lean_array_get_size(v_keys_4650_);
v___x_4660_ = lean_nat_dec_lt(v_i_4652_, v___x_4659_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
lean_dec(v_i_4652_);
lean_dec_ref(v_f_4649_);
v___x_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4661_, 0, v_acc_4653_);
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4661_);
return v___x_4662_;
}
else
{
lean_object* v_k_4663_; lean_object* v_v_4664_; lean_object* v___x_4665_; 
v_k_4663_ = lean_array_fget_borrowed(v_keys_4650_, v_i_4652_);
v_v_4664_ = lean_array_fget_borrowed(v_vals_4651_, v_i_4652_);
lean_inc_ref(v_f_4649_);
lean_inc(v___y_4657_);
lean_inc_ref(v___y_4656_);
lean_inc(v___y_4655_);
lean_inc_ref(v___y_4654_);
lean_inc(v_v_4664_);
lean_inc(v_k_4663_);
v___x_4665_ = lean_apply_8(v_f_4649_, v_acc_4653_, v_k_4663_, v_v_4664_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, lean_box(0));
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
if (lean_obj_tag(v_a_4666_) == 0)
{
lean_dec_ref_known(v_a_4666_, 1);
lean_dec(v_i_4652_);
lean_dec_ref(v_f_4649_);
return v___x_4665_;
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
lean_dec_ref_known(v___x_4665_, 1);
v_a_4667_ = lean_ctor_get(v_a_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v_a_4666_, 1);
v___x_4668_ = lean_unsigned_to_nat(1u);
v___x_4669_ = lean_nat_add(v_i_4652_, v___x_4668_);
lean_dec(v_i_4652_);
v_i_4652_ = v___x_4669_;
v_acc_4653_ = v_a_4667_;
goto _start;
}
}
else
{
lean_dec(v_i_4652_);
lean_dec_ref(v_f_4649_);
return v___x_4665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_4671_, lean_object* v_keys_4672_, lean_object* v_vals_4673_, lean_object* v_i_4674_, lean_object* v_acc_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4671_, v_keys_4672_, v_vals_4673_, v_i_4674_, v_acc_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec_ref(v_vals_4673_);
lean_dec_ref(v_keys_4672_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_4682_, lean_object* v_as_4683_, size_t v_i_4684_, size_t v_stop_4685_, lean_object* v_b_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_a_4693_; lean_object* v___y_4698_; uint8_t v___x_4701_; 
v___x_4701_ = lean_usize_dec_eq(v_i_4684_, v_stop_4685_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_array_uget_borrowed(v_as_4683_, v_i_4684_);
switch(lean_obj_tag(v___x_4702_))
{
case 0:
{
lean_object* v_key_4703_; lean_object* v_val_4704_; lean_object* v___x_4705_; 
v_key_4703_ = lean_ctor_get(v___x_4702_, 0);
v_val_4704_ = lean_ctor_get(v___x_4702_, 1);
lean_inc_ref(v_f_4682_);
lean_inc(v___y_4690_);
lean_inc_ref(v___y_4689_);
lean_inc(v___y_4688_);
lean_inc_ref(v___y_4687_);
lean_inc(v_val_4704_);
lean_inc(v_key_4703_);
v___x_4705_ = lean_apply_8(v_f_4682_, v_b_4686_, v_key_4703_, v_val_4704_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, lean_box(0));
v___y_4698_ = v___x_4705_;
goto v___jp_4697_;
}
case 1:
{
lean_object* v_node_4706_; lean_object* v___x_4707_; 
v_node_4706_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_node_4706_);
lean_inc_ref(v_f_4682_);
v___x_4707_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4682_, v_node_4706_, v_b_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
v___y_4698_ = v___x_4707_;
goto v___jp_4697_;
}
default: 
{
v_a_4693_ = v_b_4686_;
goto v___jp_4692_;
}
}
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_dec_ref(v_f_4682_);
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v_b_4686_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
v___jp_4692_:
{
size_t v___x_4694_; size_t v___x_4695_; 
v___x_4694_ = ((size_t)1ULL);
v___x_4695_ = lean_usize_add(v_i_4684_, v___x_4694_);
v_i_4684_ = v___x_4695_;
v_b_4686_ = v_a_4693_;
goto _start;
}
v___jp_4697_:
{
if (lean_obj_tag(v___y_4698_) == 0)
{
lean_object* v_a_4699_; 
v_a_4699_ = lean_ctor_get(v___y_4698_, 0);
if (lean_obj_tag(v_a_4699_) == 0)
{
lean_dec_ref(v_f_4682_);
return v___y_4698_;
}
else
{
lean_object* v_a_4700_; 
lean_inc_ref(v_a_4699_);
lean_dec_ref_known(v___y_4698_, 1);
v_a_4700_ = lean_ctor_get(v_a_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v_a_4699_, 1);
v_a_4693_ = v_a_4700_;
goto v___jp_4692_;
}
}
else
{
lean_dec_ref(v_f_4682_);
return v___y_4698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_4710_, lean_object* v_x_4711_, lean_object* v_x_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
if (lean_obj_tag(v_x_4711_) == 0)
{
lean_object* v_es_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4732_; 
v_es_4718_ = lean_ctor_get(v_x_4711_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_x_4711_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4720_ = v_x_4711_;
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_es_4718_);
lean_dec(v_x_4711_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v___x_4722_ = lean_unsigned_to_nat(0u);
v___x_4723_ = lean_array_get_size(v_es_4718_);
v___x_4724_ = lean_nat_dec_lt(v___x_4722_, v___x_4723_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4726_; 
lean_dec_ref(v_es_4718_);
lean_dec_ref(v_f_4710_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set_tag(v___x_4720_, 1);
lean_ctor_set(v___x_4720_, 0, v_x_4712_);
v___x_4726_ = v___x_4720_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_x_4712_);
v___x_4726_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; 
v___x_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
return v___x_4727_;
}
}
else
{
size_t v___x_4729_; size_t v___x_4730_; lean_object* v___x_4731_; 
lean_del_object(v___x_4720_);
v___x_4729_ = ((size_t)0ULL);
v___x_4730_ = lean_usize_of_nat(v___x_4723_);
v___x_4731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4710_, v_es_4718_, v___x_4729_, v___x_4730_, v_x_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec_ref(v_es_4718_);
return v___x_4731_;
}
}
}
else
{
lean_object* v_ks_4733_; lean_object* v_vs_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v_ks_4733_ = lean_ctor_get(v_x_4711_, 0);
lean_inc_ref(v_ks_4733_);
v_vs_4734_ = lean_ctor_get(v_x_4711_, 1);
lean_inc_ref(v_vs_4734_);
lean_dec_ref_known(v_x_4711_, 2);
v___x_4735_ = lean_unsigned_to_nat(0u);
v___x_4736_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4710_, v_ks_4733_, v_vs_4734_, v___x_4735_, v_x_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec_ref(v_vs_4734_);
lean_dec_ref(v_ks_4733_);
return v___x_4736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_4737_, lean_object* v_x_4738_, lean_object* v_x_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4737_, v_x_4738_, v_x_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_4746_, lean_object* v_as_4747_, lean_object* v_i_4748_, lean_object* v_stop_4749_, lean_object* v_b_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
size_t v_i_boxed_4756_; size_t v_stop_boxed_4757_; lean_object* v_res_4758_; 
v_i_boxed_4756_ = lean_unbox_usize(v_i_4748_);
lean_dec(v_i_4748_);
v_stop_boxed_4757_ = lean_unbox_usize(v_stop_4749_);
lean_dec(v_stop_4749_);
v_res_4758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4746_, v_as_4747_, v_i_boxed_4756_, v_stop_boxed_4757_, v_b_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec_ref(v_as_4747_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_4759_, lean_object* v_s_4760_, lean_object* v_a_4761_, lean_object* v_b_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4768_, 0, v_a_4761_);
lean_ctor_set(v___x_4768_, 1, v_b_4762_);
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
v___x_4769_ = lean_apply_7(v_f_4759_, v___x_4768_, v_s_4760_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, lean_box(0));
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4796_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4796_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4796_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
if (lean_obj_tag(v_a_4770_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4784_; 
v_a_4774_ = lean_ctor_get(v_a_4770_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v_a_4770_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4776_ = v_a_4770_;
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v_a_4770_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4781_; 
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v___x_4779_);
v___x_4781_ = v___x_4772_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4795_; 
v_a_4785_ = lean_ctor_get(v_a_4770_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_a_4770_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4787_ = v_a_4770_;
v_isShared_4788_ = v_isSharedCheck_4795_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v_a_4770_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4795_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4792_; 
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v___x_4790_);
v___x_4792_ = v___x_4772_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
v_a_4797_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v___x_4769_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4769_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_4805_, lean_object* v_s_4806_, lean_object* v_a_4807_, lean_object* v_b_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_4805_, v_s_4806_, v_a_4807_, v_b_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_4815_, lean_object* v_init_4816_, lean_object* v_f_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___f_4823_; lean_object* v___x_4824_; 
v___f_4823_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4823_, 0, v_f_4817_);
lean_inc_ref(v_map_4815_);
v___x_4824_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_4823_, v_map_4815_, v_init_4816_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4833_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4827_ = v___x_4824_;
v_isShared_4828_ = v_isSharedCheck_4833_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4824_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4833_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v_a_4829_; lean_object* v___x_4831_; 
v_a_4829_ = lean_ctor_get(v_a_4825_, 0);
lean_inc(v_a_4829_);
lean_dec(v_a_4825_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v_a_4829_);
v___x_4831_ = v___x_4827_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
v_a_4834_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4824_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4824_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_4842_, lean_object* v_init_4843_, lean_object* v_f_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4842_, v_init_4843_, v_f_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec_ref(v_map_4842_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v_env_4857_; lean_object* v___x_4858_; lean_object* v_ext_4859_; lean_object* v_toEnvExtension_4860_; lean_object* v_asyncMode_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; lean_object* v_categories_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4853_ = lean_box(1);
v___x_4854_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4855_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4856_ = lean_st_ref_get(v___y_4851_);
v_env_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc_ref_n(v_env_4857_, 2);
lean_dec(v___x_4856_);
v___x_4858_ = l_Lean_Parser_parserExtension;
v_ext_4859_ = lean_ctor_get(v___x_4858_, 1);
v_toEnvExtension_4860_ = lean_ctor_get(v_ext_4859_, 0);
v_asyncMode_4861_ = lean_ctor_get(v_toEnvExtension_4860_, 2);
v___x_4862_ = 0;
v___x_4863_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4855_, v___x_4858_, v_env_4857_, v_asyncMode_4861_, v___x_4862_);
v_categories_4864_ = lean_ctor_get(v___x_4863_, 2);
lean_inc_ref(v_categories_4864_);
lean_dec(v___x_4863_);
v___x_4865_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4864_, v___x_4865_);
lean_dec_ref(v_categories_4864_);
if (lean_obj_tag(v___x_4866_) == 1)
{
lean_object* v_val_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4898_; 
v_val_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4898_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_val_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4898_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___y_4872_; lean_object* v___x_4881_; lean_object* v_toEnvExtension_4882_; lean_object* v_exportEntriesFn_4883_; lean_object* v_asyncMode_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v_importedEntries_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v_exported_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; uint8_t v___x_4894_; 
v___x_4881_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4882_ = lean_ctor_get(v___x_4881_, 0);
v_exportEntriesFn_4883_ = lean_ctor_get(v___x_4881_, 4);
v_asyncMode_4884_ = lean_ctor_get(v_toEnvExtension_4882_, 2);
v___x_4885_ = lean_box(0);
lean_inc_ref_n(v_env_4857_, 2);
v___x_4886_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4854_, v_toEnvExtension_4882_, v_env_4857_, v_asyncMode_4884_, v___x_4885_, v___x_4862_);
v_importedEntries_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc_ref(v_importedEntries_4887_);
lean_dec(v___x_4886_);
v___x_4888_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4853_, v___x_4881_, v_env_4857_, v_asyncMode_4884_, v___x_4885_, v___x_4862_);
lean_inc_ref(v_exportEntriesFn_4883_);
v___x_4889_ = lean_apply_2(v_exportEntriesFn_4883_, v_env_4857_, v___x_4888_);
v_exported_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_exported_4890_);
lean_dec_ref(v___x_4889_);
v___x_4891_ = lean_array_push(v_importedEntries_4887_, v_exported_4890_);
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = lean_array_get_size(v___x_4891_);
v___x_4894_ = lean_nat_dec_lt(v___x_4892_, v___x_4893_);
if (v___x_4894_ == 0)
{
lean_dec_ref(v___x_4891_);
v___y_4872_ = v___x_4853_;
goto v___jp_4871_;
}
else
{
size_t v___x_4895_; size_t v___x_4896_; lean_object* v___x_4897_; 
v___x_4895_ = ((size_t)0ULL);
v___x_4896_ = lean_usize_of_nat(v___x_4893_);
v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4891_, v___x_4895_, v___x_4896_, v___x_4853_);
lean_dec_ref(v___x_4891_);
v___y_4872_ = v___x_4897_;
goto v___jp_4871_;
}
v___jp_4871_:
{
lean_object* v_tables_4873_; lean_object* v_leadingTable_4874_; lean_object* v_trailingTable_4875_; lean_object* v_firstTokens_4876_; lean_object* v_firstTokens_4877_; lean_object* v___x_4879_; 
v_tables_4873_ = lean_ctor_get(v_val_4867_, 2);
v_leadingTable_4874_ = lean_ctor_get(v_tables_4873_, 0);
v_trailingTable_4875_ = lean_ctor_get(v_tables_4873_, 2);
lean_inc(v_trailingTable_4875_);
lean_inc(v_leadingTable_4874_);
lean_inc(v_val_4867_);
v_firstTokens_4876_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4867_, v_leadingTable_4874_, v___y_4872_);
v_firstTokens_4877_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4867_, v_trailingTable_4875_, v_firstTokens_4876_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set_tag(v___x_4869_, 0);
lean_ctor_set(v___x_4869_, 0, v_firstTokens_4877_);
v___x_4879_ = v___x_4869_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_firstTokens_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
else
{
lean_object* v___x_4899_; 
lean_dec(v___x_4866_);
lean_dec_ref(v_env_4857_);
v___x_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4853_);
return v___x_4899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_4900_, lean_object* v___y_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4900_);
lean_dec(v___y_4900_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v_env_4915_; lean_object* v___x_4916_; lean_object* v_toEnvExtension_4917_; lean_object* v_exportEntriesFn_4918_; lean_object* v_asyncMode_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; lean_object* v___x_4922_; lean_object* v_importedEntries_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v_exported_4926_; lean_object* v___x_4927_; size_t v_sz_4928_; size_t v___x_4929_; lean_object* v___x_4930_; 
v___x_4911_ = lean_box(1);
v___x_4912_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4913_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4914_ = lean_st_ref_get(v_a_4909_);
v_env_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc_ref_n(v_env_4915_, 4);
lean_dec(v___x_4914_);
v___x_4916_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4917_ = lean_ctor_get(v___x_4916_, 0);
v_exportEntriesFn_4918_ = lean_ctor_get(v___x_4916_, 4);
v_asyncMode_4919_ = lean_ctor_get(v_toEnvExtension_4917_, 2);
v___x_4920_ = lean_box(0);
v___x_4921_ = 0;
v___x_4922_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4912_, v_toEnvExtension_4917_, v_env_4915_, v_asyncMode_4919_, v___x_4920_, v___x_4921_);
v_importedEntries_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc_ref(v_importedEntries_4923_);
lean_dec(v___x_4922_);
v___x_4924_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4911_, v___x_4916_, v_env_4915_, v_asyncMode_4919_, v___x_4920_, v___x_4921_);
lean_inc_ref(v_exportEntriesFn_4918_);
v___x_4925_ = lean_apply_2(v_exportEntriesFn_4918_, v_env_4915_, v___x_4924_);
v_exported_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_exported_4926_);
lean_dec_ref(v___x_4925_);
v___x_4927_ = lean_array_push(v_importedEntries_4923_, v_exported_4926_);
v_sz_4928_ = lean_array_size(v___x_4927_);
v___x_4929_ = ((size_t)0ULL);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_4927_, v_sz_4928_, v___x_4929_, v___x_4911_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
lean_dec_ref(v___x_4927_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4954_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4933_ = v___x_4930_;
v_isShared_4934_ = v_isSharedCheck_4954_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v___x_4930_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4954_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4935_; lean_object* v_ext_4936_; lean_object* v_toEnvExtension_4937_; lean_object* v_asyncMode_4938_; lean_object* v___x_4939_; lean_object* v_categories_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4935_ = l_Lean_Parser_parserExtension;
v_ext_4936_ = lean_ctor_get(v___x_4935_, 1);
v_toEnvExtension_4937_ = lean_ctor_get(v_ext_4936_, 0);
v_asyncMode_4938_ = lean_ctor_get(v_toEnvExtension_4937_, 2);
lean_inc_ref(v_env_4915_);
v___x_4939_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4913_, v___x_4935_, v_env_4915_, v_asyncMode_4938_, v___x_4921_);
v_categories_4940_ = lean_ctor_get(v___x_4939_, 2);
lean_inc_ref(v_categories_4940_);
lean_dec(v___x_4939_);
v___x_4941_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_4942_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4943_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4940_, v___x_4942_);
lean_dec_ref(v_categories_4940_);
if (lean_obj_tag(v___x_4943_) == 1)
{
lean_object* v_val_4944_; lean_object* v___x_4945_; lean_object* v_a_4946_; lean_object* v_kinds_4947_; lean_object* v___x_4948_; lean_object* v___f_4949_; lean_object* v___x_4950_; 
lean_del_object(v___x_4933_);
v_val_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc(v_val_4944_);
lean_dec_ref_known(v___x_4943_, 1);
v___x_4945_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_4909_);
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4946_);
lean_dec_ref(v___x_4945_);
v_kinds_4947_ = lean_ctor_get(v_val_4944_, 1);
lean_inc_ref(v_kinds_4947_);
lean_dec(v_val_4944_);
v___x_4948_ = lean_box(v_includeUnnamed_4905_);
v___f_4949_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4949_, 0, v_env_4915_);
lean_closure_set(v___f_4949_, 1, v___x_4920_);
lean_closure_set(v___f_4949_, 2, v_a_4931_);
lean_closure_set(v___f_4949_, 3, v_a_4946_);
lean_closure_set(v___f_4949_, 4, v___x_4948_);
v___x_4950_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_4947_, v___x_4941_, v___f_4949_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
lean_dec_ref(v_kinds_4947_);
return v___x_4950_;
}
else
{
lean_object* v___x_4952_; 
lean_dec(v___x_4943_);
lean_dec(v_a_4931_);
lean_dec_ref(v_env_4915_);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 0, v___x_4941_);
v___x_4952_ = v___x_4933_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4941_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
else
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4962_; 
lean_dec_ref(v_env_4915_);
v_a_4955_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4957_ = v___x_4930_;
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4930_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
uint8_t v_includeUnnamed_boxed_4969_; lean_object* v_res_4970_; 
v_includeUnnamed_boxed_4969_ = lean_unbox(v_includeUnnamed_4963_);
v_res_4970_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_4969_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec(v_a_4967_);
lean_dec_ref(v_a_4966_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_4971_, size_t v_sz_4972_, size_t v_i_4973_, lean_object* v_b_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4971_, v_sz_4972_, v_i_4973_, v_b_4974_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_4981_, lean_object* v_sz_4982_, lean_object* v_i_4983_, lean_object* v_b_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
size_t v_sz_boxed_4990_; size_t v_i_boxed_4991_; lean_object* v_res_4992_; 
v_sz_boxed_4990_ = lean_unbox_usize(v_sz_4982_);
lean_dec(v_sz_4982_);
v_i_boxed_4991_ = lean_unbox_usize(v_i_4983_);
lean_dec(v_i_4983_);
v_res_4992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_4981_, v_sz_boxed_4990_, v_i_boxed_4991_, v_b_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec_ref(v_as_4981_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v___x_4998_; 
v___x_4998_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4996_);
return v___x_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_5005_, lean_object* v_00_u03b2_5006_, lean_object* v_map_5007_, lean_object* v_init_5008_, lean_object* v_f_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_5007_, v_init_5008_, v_f_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_5016_, lean_object* v_00_u03b2_5017_, lean_object* v_map_5018_, lean_object* v_init_5019_, lean_object* v_f_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_5016_, v_00_u03b2_5017_, v_map_5018_, v_init_5019_, v_f_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec_ref(v_map_5018_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_5027_, lean_object* v_f_5028_, lean_object* v_init_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5028_, v_map_5027_, v_init_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_5036_, lean_object* v_f_5037_, lean_object* v_init_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_5036_, v_f_5037_, v_init_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_5045_, lean_object* v_00_u03c3_5046_, lean_object* v_00_u03b2_5047_, lean_object* v_map_5048_, lean_object* v_f_5049_, lean_object* v_init_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5056_; 
v___x_5056_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5049_, v_map_5048_, v_init_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_5057_, lean_object* v_00_u03c3_5058_, lean_object* v_00_u03b2_5059_, lean_object* v_map_5060_, lean_object* v_f_5061_, lean_object* v_init_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_5057_, v_00_u03c3_5058_, v_00_u03b2_5059_, v_map_5060_, v_f_5061_, v_init_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_5069_, lean_object* v_00_u03c3_5070_, lean_object* v_00_u03b1_5071_, lean_object* v_00_u03b2_5072_, lean_object* v_f_5073_, lean_object* v_x_5074_, lean_object* v_x_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5073_, v_x_5074_, v_x_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_5082_, lean_object* v_00_u03c3_5083_, lean_object* v_00_u03b1_5084_, lean_object* v_00_u03b2_5085_, lean_object* v_f_5086_, lean_object* v_x_5087_, lean_object* v_x_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_5082_, v_00_u03c3_5083_, v_00_u03b1_5084_, v_00_u03b2_5085_, v_f_5086_, v_x_5087_, v_x_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_5095_, lean_object* v_00_u03b2_5096_, lean_object* v_00_u03c3_5097_, lean_object* v_00_u03c3_5098_, lean_object* v_f_5099_, lean_object* v_as_5100_, size_t v_i_5101_, size_t v_stop_5102_, lean_object* v_b_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v___x_5109_; 
v___x_5109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5099_, v_as_5100_, v_i_5101_, v_stop_5102_, v_b_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5110_, lean_object* v_00_u03b2_5111_, lean_object* v_00_u03c3_5112_, lean_object* v_00_u03c3_5113_, lean_object* v_f_5114_, lean_object* v_as_5115_, lean_object* v_i_5116_, lean_object* v_stop_5117_, lean_object* v_b_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
size_t v_i_boxed_5124_; size_t v_stop_boxed_5125_; lean_object* v_res_5126_; 
v_i_boxed_5124_ = lean_unbox_usize(v_i_5116_);
lean_dec(v_i_5116_);
v_stop_boxed_5125_ = lean_unbox_usize(v_stop_5117_);
lean_dec(v_stop_5117_);
v_res_5126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_5110_, v_00_u03b2_5111_, v_00_u03c3_5112_, v_00_u03c3_5113_, v_f_5114_, v_as_5115_, v_i_boxed_5124_, v_stop_boxed_5125_, v_b_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_as_5115_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_5127_, lean_object* v_00_u03c3_5128_, lean_object* v_00_u03b1_5129_, lean_object* v_00_u03b2_5130_, lean_object* v_f_5131_, lean_object* v_keys_5132_, lean_object* v_vals_5133_, lean_object* v_heq_5134_, lean_object* v_i_5135_, lean_object* v_acc_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_5131_, v_keys_5132_, v_vals_5133_, v_i_5135_, v_acc_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_5143_, lean_object* v_00_u03c3_5144_, lean_object* v_00_u03b1_5145_, lean_object* v_00_u03b2_5146_, lean_object* v_f_5147_, lean_object* v_keys_5148_, lean_object* v_vals_5149_, lean_object* v_heq_5150_, lean_object* v_i_5151_, lean_object* v_acc_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_5143_, v_00_u03c3_5144_, v_00_u03b1_5145_, v_00_u03b2_5146_, v_f_5147_, v_keys_5148_, v_vals_5149_, v_heq_5150_, v_i_5151_, v_acc_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec_ref(v_vals_5149_);
lean_dec_ref(v_keys_5148_);
return v_res_5158_;
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
