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
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
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
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_56_ = stack[0].m_obj;
lean_object* v_x_57_ = stack[1].m_obj;
lean_object* v_a_58_ = stack[2].m_obj;
lean_object* v_a_59_ = stack[3].m_obj;
lean_object* v_a_60_ = stack[4].m_obj;
lean_object* v_res_399_;
v_res_399_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v_x_56_, v_x_57_, v_a_58_, v_a_59_, v_a_60_);
stack->m_obj
 = v_res_399_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(lean_object* v_x_400_, size_t v_sz_401_, size_t v_i_402_, lean_object* v_bs_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_usize_dec_lt(v_i_402_, v_sz_401_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v_x_400_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_bs_403_);
return v___x_409_;
}
else
{
lean_object* v_v_410_; lean_object* v___x_411_; lean_object* v_bs_x27_412_; lean_object* v___x_413_; 
v_v_410_ = lean_array_uget(v_bs_403_, v_i_402_);
v___x_411_ = lean_unsigned_to_nat(0u);
v_bs_x27_412_ = lean_array_uset(v_bs_403_, v_i_402_, v___x_411_);
lean_inc_ref(v_x_400_);
v___x_413_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v_x_400_, v_v_410_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_402_, v___x_415_);
v___x_417_ = lean_array_uset(v_bs_x27_412_, v_i_402_, v_a_414_);
v_i_402_ = v___x_416_;
v_bs_403_ = v___x_417_;
goto _start;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_bs_x27_412_);
lean_dec_ref(v_x_400_);
v_a_419_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_413_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_413_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_400_ = stack[0].m_obj;
size_t v_sz_401_ = stack[1].m_num;
size_t v_i_402_ = stack[2].m_num;
lean_object* v_bs_403_ = stack[3].m_obj;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v___y_405_ = stack[5].m_obj;
lean_object* v___y_406_ = stack[6].m_obj;
lean_object* v_res_427_;
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_400_, v_sz_401_, v_i_402_, v_bs_403_, v___y_404_, v___y_405_, v___y_406_);
stack->m_obj
 = v_res_427_;
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(lean_object* v_x_428_, size_t v_sz_429_, size_t v___x_430_, lean_object* v_content_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_428_, v_sz_429_, v___x_430_, v_content_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_Doc_joinInlines(v_a_437_);
lean_dec(v_a_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_436_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_436_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_428_ = stack[0].m_obj;
size_t v_sz_429_ = stack[1].m_num;
size_t v___x_430_ = stack[2].m_num;
lean_object* v_content_431_ = stack[3].m_obj;
lean_object* v___y_432_ = stack[4].m_obj;
lean_object* v___y_433_ = stack[5].m_obj;
lean_object* v___y_434_ = stack[6].m_obj;
lean_object* v_res_454_;
v_res_454_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(v_x_428_, v_sz_429_, v___x_430_, v_content_431_, v___y_432_, v___y_433_, v___y_434_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4___boxed(lean_object* v_x_455_, lean_object* v_sz_456_, lean_object* v_i_457_, lean_object* v_bs_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
size_t v_sz_boxed_463_; size_t v_i_boxed_464_; lean_object* v_res_465_; 
v_sz_boxed_463_ = lean_unbox_usize(v_sz_456_);
lean_dec(v_sz_456_);
v_i_boxed_464_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2_spec__4(v_x_455_, v_sz_boxed_463_, v_i_boxed_464_, v_bs_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__9(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_zero_468_; uint8_t v_isZero_469_; 
v_zero_468_ = lean_unsigned_to_nat(0u);
v_isZero_469_ = lean_nat_dec_eq(v_x_466_, v_zero_468_);
if (v_isZero_469_ == 1)
{
lean_dec(v_x_466_);
return v_x_467_;
}
else
{
uint32_t v___x_470_; lean_object* v_one_471_; lean_object* v_n_472_; lean_object* v___x_473_; 
v___x_470_ = 32;
v_one_471_ = lean_unsigned_to_nat(1u);
v_n_472_ = lean_nat_sub(v_x_466_, v_one_471_);
lean_dec(v_x_466_);
v___x_473_ = lean_string_push(v_x_467_, v___x_470_);
v_x_466_ = v_n_472_;
v_x_467_ = v___x_473_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(size_t v_sz_479_, size_t v_i_480_, lean_object* v_bs_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_480_, v_sz_479_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_bs_481_);
return v___x_487_;
}
else
{
lean_object* v_v_488_; lean_object* v___x_489_; lean_object* v_bs_x27_490_; size_t v_sz_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_v_488_ = lean_array_uget(v_bs_481_, v_i_480_);
v___x_489_ = lean_unsigned_to_nat(0u);
v_bs_x27_490_ = lean_array_uset(v_bs_481_, v_i_480_, v___x_489_);
v_sz_491_ = lean_array_size(v_v_488_);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_491_, v___x_492_, v_v_488_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0));
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1));
v___x_497_ = l_Lean_Doc_joinBlocks(v_a_494_);
lean_dec(v_a_494_);
v___x_498_ = l_Lean_Doc_prefixListLines(v___x_495_, v___x_496_, v___x_497_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_480_, v___x_499_);
v___x_501_ = lean_array_uset(v_bs_x27_490_, v_i_480_, v___x_498_);
v_i_480_ = v___x_500_;
v_bs_481_ = v___x_501_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_490_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_479_ = stack[0].m_num;
size_t v_i_480_ = stack[1].m_num;
lean_object* v_bs_481_ = stack[2].m_obj;
lean_object* v___y_482_ = stack[3].m_obj;
lean_object* v___y_483_ = stack[4].m_obj;
lean_object* v___y_484_ = stack[5].m_obj;
lean_object* v_res_503_;
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_479_, v_i_480_, v_bs_481_, v___y_482_, v___y_483_, v___y_484_);
stack->m_obj
 = v_res_503_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_b_508_);
return v___x_514_;
}
else
{
lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_550_; 
v_fst_515_ = lean_ctor_get(v_b_508_, 0);
v_snd_516_ = lean_ctor_get(v_b_508_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_b_508_);
if (v_isSharedCheck_550_ == 0)
{
v___x_518_ = v_b_508_;
v_isShared_519_ = v_isSharedCheck_550_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snd_516_);
lean_inc(v_fst_515_);
lean_dec(v_b_508_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_550_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v_a_521_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
lean_inc(v_snd_516_);
v___x_522_ = l_Nat_reprFast(v_snd_516_);
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___closed__0));
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
v___x_525_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_526_ = lean_string_utf8_byte_size(v___x_524_);
v___x_527_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__9(v___x_526_, v___x_525_);
v_sz_528_ = lean_array_size(v_a_521_);
v___x_529_ = ((size_t)0ULL);
lean_inc(v_a_521_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_528_, v___x_529_, v_a_521_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = l_Lean_Doc_joinBlocks(v_a_531_);
lean_dec(v_a_531_);
v___x_533_ = l_Lean_Doc_prefixListLines(v___x_524_, v___x_527_, v___x_532_);
v___x_534_ = lean_array_push(v_fst_515_, v___x_533_);
v___x_535_ = lean_nat_add(v_snd_516_, v___x_520_);
lean_dec(v_snd_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_535_);
lean_ctor_set(v___x_518_, 0, v___x_534_);
v___x_537_ = v___x_518_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_541_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
size_t v___x_538_; size_t v___x_539_; 
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_507_, v___x_538_);
v_i_507_ = v___x_539_;
v_b_508_ = v___x_537_;
goto _start;
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_524_);
lean_del_object(v___x_518_);
lean_dec(v_snd_516_);
lean_dec(v_fst_515_);
v_a_542_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_530_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_530_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_505_ = stack[0].m_obj;
size_t v_sz_506_ = stack[1].m_num;
size_t v_i_507_ = stack[2].m_num;
lean_object* v_b_508_ = stack[3].m_obj;
lean_object* v___y_509_ = stack[4].m_obj;
lean_object* v___y_510_ = stack[5].m_obj;
lean_object* v___y_511_ = stack[6].m_obj;
lean_object* v_res_551_;
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_as_505_, v_sz_506_, v_i_507_, v_b_508_, v___y_509_, v___y_510_, v___y_511_);
stack->m_obj
 = v_res_551_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(size_t v_sz_557_, size_t v_i_558_, lean_object* v_bs_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = lean_usize_dec_lt(v_i_558_, v_sz_557_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_bs_559_);
return v___x_565_;
}
else
{
lean_object* v_v_566_; lean_object* v___x_567_; lean_object* v_term_568_; lean_object* v_desc_569_; lean_object* v___x_570_; lean_object* v_bs_x27_571_; lean_object* v_a_573_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_v_566_ = lean_array_uget_borrowed(v_bs_559_, v_i_558_);
v___x_567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
v_term_568_ = lean_ctor_get(v_v_566_, 0);
lean_inc_ref(v_term_568_);
v_desc_569_ = lean_ctor_get(v_v_566_, 1);
lean_inc_ref(v_desc_569_);
v___x_570_ = lean_unsigned_to_nat(0u);
v_bs_x27_571_ = lean_array_uset(v_bs_559_, v_i_558_, v___x_570_);
v___x_578_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_578_, 0, v_term_568_);
v___x_579_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_567_, v___x_578_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v_sz_581_ = lean_array_size(v_desc_569_);
v___x_582_ = ((size_t)0ULL);
lean_inc_ref(v_desc_569_);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_581_, v___x_582_, v_desc_569_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___y_586_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_mk_empty_array_with_capacity(v___x_590_);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__2));
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = lean_mk_empty_array_with_capacity(v___x_593_);
v___x_595_ = lean_array_push(v___x_594_, v_a_580_);
v___x_596_ = lean_array_push(v___x_595_, v___x_592_);
v___x_597_ = l_Lean_Doc_joinInlines(v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = lean_array_get_size(v_desc_569_);
lean_dec_ref(v_desc_569_);
v___x_599_ = lean_nat_dec_le(v___x_598_, v___x_590_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_array_push(v___x_591_, v___x_597_);
v___x_601_ = l_Array_append___redArg(v___x_600_, v_a_584_);
lean_dec(v_a_584_);
v___x_602_ = l_Lean_Doc_joinBlocks(v___x_601_);
lean_dec_ref(v___x_601_);
v___y_586_ = v___x_602_;
goto v___jp_585_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec_ref(v___x_591_);
v___x_603_ = l_Lean_Doc_joinBlocks(v_a_584_);
lean_dec(v_a_584_);
v___x_604_ = l_Array_append___redArg(v___x_597_, v___x_603_);
lean_dec_ref(v___x_603_);
v___y_586_ = v___x_604_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0));
v___x_588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1));
v___x_589_ = l_Lean_Doc_prefixListLines(v___x_587_, v___x_588_, v___y_586_);
v_a_573_ = v___x_589_;
goto v___jp_572_;
}
}
else
{
lean_dec(v_a_580_);
lean_dec_ref(v_bs_x27_571_);
lean_dec_ref(v_desc_569_);
return v___x_583_;
}
}
else
{
lean_dec_ref(v_desc_569_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_579_, 1);
v_a_573_ = v_a_605_;
goto v___jp_572_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_bs_x27_571_);
v_a_606_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_579_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_579_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
v___jp_572_:
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_558_, v___x_574_);
v___x_576_ = lean_array_uset(v_bs_x27_571_, v_i_558_, v_a_573_);
v_i_558_ = v___x_575_;
v_bs_559_ = v___x_576_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_sz_557_ = stack[0].m_num;
size_t v_i_558_ = stack[1].m_num;
lean_object* v_bs_559_ = stack[2].m_obj;
lean_object* v___y_560_ = stack[3].m_obj;
lean_object* v___y_561_ = stack[4].m_obj;
lean_object* v___y_562_ = stack[5].m_obj;
lean_object* v_res_614_;
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_557_, v_i_558_, v_bs_559_, v___y_560_, v___y_561_, v___y_562_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed(lean_object* v_x_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_x_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed(lean_object* v_sz_624_, lean_object* v___x_625_, lean_object* v_content_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
size_t v_sz_boxed_631_; size_t v___x_7342__boxed_632_; lean_object* v_res_633_; 
v_sz_boxed_631_ = lean_unbox_usize(v_sz_624_);
lean_dec(v_sz_624_);
v___x_7342__boxed_632_ = lean_unbox_usize(v___x_625_);
lean_dec(v___x_625_);
v_res_633_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(v_sz_boxed_631_, v___x_7342__boxed_632_, v_content_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
return v_res_633_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(lean_object* v_x_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
switch(lean_obj_tag(v_x_634_))
{
case 0:
{
lean_object* v_contents_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_648_; 
v_contents_639_ = lean_ctor_get(v_x_634_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_648_ == 0)
{
v___x_641_ = v_x_634_;
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_contents_639_);
lean_dec(v_x_634_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 9);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_contents_639_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_643_, v___x_645_, v_a_635_, v_a_636_, v_a_637_);
return v___x_646_;
}
}
}
case 1:
{
lean_object* v_content_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_content_649_ = lean_ctor_get(v_x_634_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_x_634_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_content_649_);
lean_dec(v_x_634_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 0);
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
case 2:
{
lean_object* v_items_658_; size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; 
v_items_658_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_items_658_);
lean_dec_ref_known(v_x_634_, 1);
v_sz_659_ = lean_array_size(v_items_658_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_659_, v___x_660_, v_items_658_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Lean_Doc_joinBlocks(v_a_662_);
lean_dec(v_a_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_a_671_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_661_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_661_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
case 3:
{
lean_object* v_start_679_; lean_object* v_items_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_714_; 
v_start_679_ = lean_ctor_get(v_x_634_, 0);
v_items_680_ = lean_ctor_get(v_x_634_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_714_ == 0)
{
v___x_682_ = v_x_634_;
v_isShared_683_ = v_isSharedCheck_714_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_items_680_);
lean_inc(v_start_679_);
lean_dec(v_x_634_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_714_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_out_684_; lean_object* v___y_686_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_out_684_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2));
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = l_Int_toNat(v_start_679_);
lean_dec(v_start_679_);
v___x_713_ = lean_nat_dec_le(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v___x_712_);
v___y_686_ = v___x_711_;
goto v___jp_685_;
}
else
{
v___y_686_ = v___x_712_;
goto v___jp_685_;
}
v___jp_685_:
{
lean_object* v___x_688_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
lean_ctor_set(v___x_682_, 1, v___y_686_);
lean_ctor_set(v___x_682_, 0, v_out_684_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_out_684_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___y_686_);
v___x_688_ = v_reuseFailAlloc_710_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; 
v_sz_689_ = lean_array_size(v_items_680_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_items_680_, v_sz_689_, v___x_690_, v___x_688_, v_a_635_, v_a_636_, v_a_637_);
lean_dec_ref(v_items_680_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_701_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_fst_696_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_fst_696_);
lean_dec(v_a_692_);
v___x_697_ = l_Lean_Doc_joinBlocks(v_fst_696_);
lean_dec(v_fst_696_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_697_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_a_702_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_691_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_691_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_715_; size_t v_sz_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_items_715_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_items_715_);
lean_dec_ref_known(v_x_634_, 1);
v_sz_716_ = lean_array_size(v_items_715_);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_716_, v___x_717_, v_items_715_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = l_Lean_Doc_joinBlocks(v_a_719_);
lean_dec(v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_718_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_718_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
case 5:
{
lean_object* v_items_736_; size_t v_sz_737_; size_t v___x_738_; lean_object* v___x_739_; 
v_items_736_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_items_736_);
lean_dec_ref_known(v_x_634_, 1);
v_sz_737_ = lean_array_size(v_items_736_);
v___x_738_ = ((size_t)0ULL);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_737_, v___x_738_, v_items_736_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_750_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_750_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_750_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_750_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_744_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__0));
v___x_745_ = l_Lean_Doc_joinBlocks(v_a_740_);
lean_dec(v_a_740_);
v___x_746_ = l_Lean_Doc_prefixLines(v___x_744_, v___x_745_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_746_);
v___x_748_ = v___x_742_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_739_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_739_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
case 6:
{
lean_object* v_content_759_; size_t v_sz_760_; size_t v___x_761_; lean_object* v___x_762_; 
v_content_759_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_content_759_);
lean_dec_ref_known(v_x_634_, 1);
v_sz_760_ = lean_array_size(v_content_759_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_760_, v___x_761_, v_content_759_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = l_Lean_Doc_joinBlocks(v_a_763_);
lean_dec(v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v_a_772_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_762_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
default: 
{
lean_object* v_container_780_; 
v_container_780_ = lean_ctor_get(v_x_634_, 0);
if (lean_obj_tag(v_container_780_) == 0)
{
lean_object* v_content_781_; lean_object* v_val_782_; lean_object* v___x_783_; lean_object* v___x_784_; size_t v_sz_785_; size_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_fallback_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_inc_ref(v_container_780_);
v_content_781_ = lean_ctor_get(v_x_634_, 1);
lean_inc_ref_n(v_content_781_, 2);
lean_dec_ref_known(v_x_634_, 2);
v_val_782_ = lean_ctor_get(v_container_780_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v_container_780_, 1);
v___x_783_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__1));
v___x_784_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed), 5, 0);
v_sz_785_ = lean_array_size(v_content_781_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_box_usize(v_sz_785_);
v___x_788_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1));
v_fallback_789_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed), 7, 3);
lean_closure_set(v_fallback_789_, 0, v___x_787_);
lean_closure_set(v_fallback_789_, 1, v___x_788_);
lean_closure_set(v_fallback_789_, 2, v_content_781_);
v___x_790_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_782_);
v___x_791_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_790_, v_a_636_, v_a_637_);
lean_dec(v___x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
if (lean_obj_tag(v_a_792_) == 0)
{
lean_object* v___x_793_; 
lean_dec_ref(v_fallback_789_);
lean_dec_ref(v___x_784_);
lean_dec(v_val_782_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_785_, v___x_786_, v_content_781_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_Lean_Doc_joinBlocks(v_a_794_);
lean_dec(v_a_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_a_803_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_793_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_793_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_val_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_val_811_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v_a_792_, 1);
v___x_812_ = lean_apply_4(v_val_811_, v___x_783_, v___x_784_, v_val_782_, v_content_781_);
v___x_813_ = l_Lean_Doc_withRendererFallback(v_fallback_789_, v___x_812_, v_a_635_, v_a_636_, v_a_637_);
return v___x_813_;
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_fallback_789_);
lean_dec_ref(v___x_784_);
lean_dec(v_val_782_);
lean_dec_ref(v_content_781_);
v_a_814_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_791_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_791_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_content_822_; size_t v_sz_823_; size_t v___x_824_; lean_object* v___x_825_; 
v_content_822_ = lean_ctor_get(v_x_634_, 1);
lean_inc_ref(v_content_822_);
lean_dec_ref_known(v_x_634_, 2);
v_sz_823_ = lean_array_size(v_content_822_);
v___x_824_ = ((size_t)0ULL);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_823_, v___x_824_, v_content_822_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = l_Lean_Doc_joinBlocks(v_a_826_);
lean_dec(v_a_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_825_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_825_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_634_ = stack[0].m_obj;
lean_object* v_a_635_ = stack[1].m_obj;
lean_object* v_a_636_ = stack[2].m_obj;
lean_object* v_a_637_ = stack[3].m_obj;
lean_object* v_res_843_;
v_res_843_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_x_634_, v_a_635_, v_a_636_, v_a_637_);
stack->m_obj
 = v_res_843_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(size_t v_sz_844_, size_t v_i_845_, lean_object* v_bs_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_lt(v_i_845_, v_sz_844_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_bs_846_);
return v___x_852_;
}
else
{
lean_object* v_v_853_; lean_object* v___x_854_; lean_object* v_bs_x27_855_; lean_object* v___x_856_; 
v_v_853_ = lean_array_uget(v_bs_846_, v_i_845_);
v___x_854_ = lean_unsigned_to_nat(0u);
v_bs_x27_855_ = lean_array_uset(v_bs_846_, v_i_845_, v___x_854_);
v___x_856_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_v_853_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_845_, v___x_858_);
v___x_860_ = lean_array_uset(v_bs_x27_855_, v_i_845_, v_a_857_);
v_i_845_ = v___x_859_;
v_bs_846_ = v___x_860_;
goto _start;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v_bs_x27_855_);
v_a_862_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_856_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_856_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_844_ = stack[0].m_num;
size_t v_i_845_ = stack[1].m_num;
lean_object* v_bs_846_ = stack[2].m_obj;
lean_object* v___y_847_ = stack[3].m_obj;
lean_object* v___y_848_ = stack[4].m_obj;
lean_object* v___y_849_ = stack[5].m_obj;
lean_object* v_res_870_;
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_844_, v_i_845_, v_bs_846_, v___y_847_, v___y_848_, v___y_849_);
stack->m_obj
 = v_res_870_;
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(size_t v_sz_871_, size_t v___x_872_, lean_object* v_content_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_871_, v___x_872_, v_content_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_887_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_887_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_887_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_887_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = l_Lean_Doc_joinBlocks(v_a_879_);
lean_dec(v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_878_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_878_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_871_ = stack[0].m_num;
size_t v___x_872_ = stack[1].m_num;
lean_object* v_content_873_ = stack[2].m_obj;
lean_object* v___y_874_ = stack[3].m_obj;
lean_object* v___y_875_ = stack[4].m_obj;
lean_object* v___y_876_ = stack[5].m_obj;
lean_object* v_res_896_;
v_res_896_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(v_sz_871_, v___x_872_, v_content_873_, v___y_874_, v___y_875_, v___y_876_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7___boxed(lean_object* v_sz_897_, lean_object* v_i_898_, lean_object* v_bs_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_897_);
lean_dec(v_sz_897_);
v_i_boxed_905_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_boxed_904_, v_i_boxed_905_, v_bs_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___boxed(lean_object* v_sz_907_, lean_object* v_i_908_, lean_object* v_bs_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
size_t v_sz_boxed_914_; size_t v_i_boxed_915_; lean_object* v_res_916_; 
v_sz_boxed_914_ = lean_unbox_usize(v_sz_907_);
lean_dec(v_sz_907_);
v_i_boxed_915_ = lean_unbox_usize(v_i_908_);
lean_dec(v_i_908_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_boxed_914_, v_i_boxed_915_, v_bs_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___boxed(lean_object* v_as_917_, lean_object* v_sz_918_, lean_object* v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
size_t v_sz_boxed_925_; size_t v_i_boxed_926_; lean_object* v_res_927_; 
v_sz_boxed_925_ = lean_unbox_usize(v_sz_918_);
lean_dec(v_sz_918_);
v_i_boxed_926_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_as_917_, v_sz_boxed_925_, v_i_boxed_926_, v_b_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v_as_917_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___boxed(lean_object* v_sz_928_, lean_object* v_i_929_, lean_object* v_bs_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v_sz_boxed_935_ = lean_unbox_usize(v_sz_928_);
lean_dec(v_sz_928_);
v_i_boxed_936_ = lean_unbox_usize(v_i_929_);
lean_dec(v_i_929_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_boxed_935_, v_i_boxed_936_, v_bs_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
return v_res_937_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(size_t v_sz_938_, size_t v_i_939_, lean_object* v_bs_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_939_, v_sz_938_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_bs_940_);
return v___x_946_;
}
else
{
lean_object* v_v_947_; lean_object* v___x_948_; lean_object* v_bs_x27_949_; lean_object* v___x_950_; 
v_v_947_ = lean_array_uget(v_bs_940_, v_i_939_);
v___x_948_ = lean_unsigned_to_nat(0u);
v_bs_x27_949_ = lean_array_uset(v_bs_940_, v_i_939_, v___x_948_);
v___x_950_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_v_947_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_939_, v___x_952_);
v___x_954_ = lean_array_uset(v_bs_x27_949_, v_i_939_, v_a_951_);
v_i_939_ = v___x_953_;
v_bs_940_ = v___x_954_;
goto _start;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_bs_x27_949_);
v_a_956_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_950_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_950_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_938_ = stack[0].m_num;
size_t v_i_939_ = stack[1].m_num;
lean_object* v_bs_940_ = stack[2].m_obj;
lean_object* v___y_941_ = stack[3].m_obj;
lean_object* v___y_942_ = stack[4].m_obj;
lean_object* v___y_943_ = stack[5].m_obj;
lean_object* v_res_964_;
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_938_, v_i_939_, v_bs_940_, v___y_941_, v___y_942_, v___y_943_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed(lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_bs_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
size_t v_sz_boxed_972_; size_t v_i_boxed_973_; lean_object* v_res_974_; 
v_sz_boxed_972_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_973_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_boxed_972_, v_i_boxed_973_, v_bs_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
lean_object* v_zero_977_; uint8_t v_isZero_978_; 
v_zero_977_ = lean_unsigned_to_nat(0u);
v_isZero_978_ = lean_nat_dec_eq(v_x_975_, v_zero_977_);
if (v_isZero_978_ == 1)
{
lean_dec(v_x_975_);
return v_x_976_;
}
else
{
uint32_t v___x_979_; lean_object* v_one_980_; lean_object* v_n_981_; lean_object* v___x_982_; 
v___x_979_ = 35;
v_one_980_ = lean_unsigned_to_nat(1u);
v_n_981_ = lean_nat_sub(v_x_975_, v_one_980_);
lean_dec(v_x_975_);
v___x_982_ = lean_string_push(v_x_976_, v___x_979_);
v_x_975_ = v_n_981_;
v_x_976_ = v___x_982_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(size_t v_sz_984_, size_t v_i_985_, lean_object* v_bs_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_lt(v_i_985_, v_sz_984_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_bs_986_);
return v___x_992_;
}
else
{
lean_object* v_v_993_; lean_object* v___x_994_; lean_object* v_bs_x27_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_v_993_ = lean_array_uget(v_bs_986_, v_i_985_);
v___x_994_ = lean_unsigned_to_nat(0u);
v_bs_x27_995_ = lean_array_uset(v_bs_986_, v_i_985_, v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
v___x_997_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_996_, v_v_993_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_985_, v___x_999_);
v___x_1001_ = lean_array_uset(v_bs_x27_995_, v_i_985_, v_a_998_);
v_i_985_ = v___x_1000_;
v_bs_986_ = v___x_1001_;
goto _start;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_bs_x27_995_);
v_a_1003_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_997_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_997_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_984_ = stack[0].m_num;
size_t v_i_985_ = stack[1].m_num;
lean_object* v_bs_986_ = stack[2].m_obj;
lean_object* v___y_987_ = stack[3].m_obj;
lean_object* v___y_988_ = stack[4].m_obj;
lean_object* v___y_989_ = stack[5].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_984_, v_i_985_, v_bs_986_, v___y_987_, v___y_988_, v___y_989_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___boxed(lean_object* v_sz_1012_, lean_object* v_i_1013_, lean_object* v_bs_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
size_t v_sz_boxed_1019_; size_t v_i_boxed_1020_; lean_object* v_res_1021_; 
v_sz_boxed_1019_ = lean_unbox_usize(v_sz_1012_);
lean_dec(v_sz_1012_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1013_);
lean_dec(v_i_1013_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_boxed_1019_, v_i_boxed_1020_, v_bs_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
return v_res_1021_;
}
}
lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(lean_object* v_level_1023_, lean_object* v_part_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_title_1029_; lean_object* v_content_1030_; lean_object* v_subParts_1031_; size_t v_sz_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v_title_1029_ = lean_ctor_get(v_part_1024_, 0);
lean_inc_ref(v_title_1029_);
v_content_1030_ = lean_ctor_get(v_part_1024_, 3);
lean_inc_ref(v_content_1030_);
v_subParts_1031_ = lean_ctor_get(v_part_1024_, 4);
lean_inc_ref(v_subParts_1031_);
lean_dec_ref(v_part_1024_);
v_sz_1032_ = lean_array_size(v_title_1029_);
v___x_1033_ = ((size_t)0ULL);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_1032_, v___x_1033_, v_title_1029_, v_a_1025_, v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; size_t v_sz_1047_; lean_object* v___x_1048_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_1037_ = lean_unsigned_to_nat(1u);
v___x_1038_ = lean_nat_add(v_level_1023_, v___x_1037_);
lean_inc(v___x_1038_);
v___x_1039_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(v___x_1038_, v___x_1036_);
v___x_1040_ = ((lean_object*)(l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___closed__0));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_mk_empty_array_with_capacity(v___x_1037_);
lean_inc_ref_n(v___x_1042_, 2);
v___x_1043_ = lean_array_push(v___x_1042_, v___x_1041_);
v___x_1044_ = lean_array_push(v___x_1042_, v___x_1043_);
v___x_1045_ = l_Array_append___redArg(v___x_1044_, v_a_1035_);
lean_dec(v_a_1035_);
v___x_1046_ = l_Lean_Doc_joinInlines(v___x_1045_);
lean_dec_ref(v___x_1045_);
v_sz_1047_ = lean_array_size(v_content_1030_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_1047_, v___x_1033_, v_content_1030_, v_a_1025_, v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; size_t v_sz_1050_; lean_object* v___x_1051_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v_sz_1050_ = lean_array_size(v_subParts_1031_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1038_, v_sz_1050_, v___x_1033_, v_subParts_1031_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v___x_1038_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1063_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1056_ = lean_array_push(v___x_1042_, v___x_1046_);
v___x_1057_ = l_Array_append___redArg(v___x_1056_, v_a_1049_);
lean_dec(v_a_1049_);
v___x_1058_ = l_Array_append___redArg(v___x_1057_, v_a_1052_);
lean_dec(v_a_1052_);
v___x_1059_ = l_Lean_Doc_joinBlocks(v___x_1058_);
lean_dec_ref(v___x_1058_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1059_);
v___x_1061_ = v___x_1054_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_a_1049_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___x_1042_);
v_a_1064_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1051_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1051_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___x_1042_);
lean_dec(v___x_1038_);
lean_dec_ref(v_subParts_1031_);
v_a_1072_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1048_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1048_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v_subParts_1031_);
lean_dec_ref(v_content_1030_);
v_a_1080_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1034_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1034_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_1023_ = stack[0].m_obj;
lean_object* v_part_1024_ = stack[1].m_obj;
lean_object* v_a_1025_ = stack[2].m_obj;
lean_object* v_a_1026_ = stack[3].m_obj;
lean_object* v_a_1027_ = stack[4].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1023_, v_part_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
stack->m_obj
 = v_res_1088_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(lean_object* v___x_1089_, size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_bs_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_usize_dec_lt(v_i_1091_, v_sz_1090_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_bs_1092_);
return v___x_1098_;
}
else
{
lean_object* v_v_1099_; lean_object* v___x_1100_; lean_object* v_bs_x27_1101_; lean_object* v___x_1102_; 
v_v_1099_ = lean_array_uget(v_bs_1092_, v_i_1091_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v_bs_x27_1101_ = lean_array_uset(v_bs_1092_, v_i_1091_, v___x_1100_);
v___x_1102_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v___x_1089_, v_v_1099_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = ((size_t)1ULL);
v___x_1105_ = lean_usize_add(v_i_1091_, v___x_1104_);
v___x_1106_ = lean_array_uset(v_bs_x27_1101_, v_i_1091_, v_a_1103_);
v_i_1091_ = v___x_1105_;
v_bs_1092_ = v___x_1106_;
goto _start;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_bs_x27_1101_);
v_a_1108_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1102_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1102_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1089_ = stack[0].m_obj;
size_t v_sz_1090_ = stack[1].m_num;
size_t v_i_1091_ = stack[2].m_num;
lean_object* v_bs_1092_ = stack[3].m_obj;
lean_object* v___y_1093_ = stack[4].m_obj;
lean_object* v___y_1094_ = stack[5].m_obj;
lean_object* v___y_1095_ = stack[6].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1089_, v_sz_1090_, v_i_1091_, v_bs_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg___boxed(lean_object* v___x_1117_, lean_object* v_sz_1118_, lean_object* v_i_1119_, lean_object* v_bs_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
size_t v_sz_boxed_1125_; size_t v_i_boxed_1126_; lean_object* v_res_1127_; 
v_sz_boxed_1125_ = lean_unbox_usize(v_sz_1118_);
lean_dec(v_sz_1118_);
v_i_boxed_1126_ = lean_unbox_usize(v_i_1119_);
lean_dec(v_i_1119_);
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1117_, v_sz_boxed_1125_, v_i_boxed_1126_, v_bs_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v___x_1117_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___boxed(lean_object* v_level_1128_, lean_object* v_part_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1128_, v_part_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec(v_level_1128_);
return v_res_1134_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(size_t v_sz_1135_, size_t v_i_1136_, lean_object* v_bs_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_lt(v_i_1136_, v_sz_1135_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_bs_1137_);
return v___x_1143_;
}
else
{
lean_object* v_v_1144_; lean_object* v___x_1145_; lean_object* v_bs_x27_1146_; lean_object* v___x_1147_; 
v_v_1144_ = lean_array_uget(v_bs_1137_, v_i_1136_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v_bs_x27_1146_ = lean_array_uset(v_bs_1137_, v_i_1136_, v___x_1145_);
v___x_1147_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v___x_1145_, v_v_1144_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1136_, v___x_1149_);
v___x_1151_ = lean_array_uset(v_bs_x27_1146_, v_i_1136_, v_a_1148_);
v_i_1136_ = v___x_1150_;
v_bs_1137_ = v___x_1151_;
goto _start;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_bs_x27_1146_);
v_a_1153_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1147_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1135_ = stack[0].m_num;
size_t v_i_1136_ = stack[1].m_num;
lean_object* v_bs_1137_ = stack[2].m_obj;
lean_object* v___y_1138_ = stack[3].m_obj;
lean_object* v___y_1139_ = stack[4].m_obj;
lean_object* v___y_1140_ = stack[5].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_1135_, v_i_1136_, v_bs_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4___boxed(lean_object* v_sz_1162_, lean_object* v_i_1163_, lean_object* v_bs_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
size_t v_sz_boxed_1169_; size_t v_i_boxed_1170_; lean_object* v_res_1171_; 
v_sz_boxed_1169_ = lean_unbox_usize(v_sz_1162_);
lean_dec(v_sz_1162_);
v_i_boxed_1170_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_boxed_1169_, v_i_boxed_1170_, v_bs_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
return v_res_1171_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(lean_object* v_fst_1172_, lean_object* v_snd_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
size_t v_sz_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_sz_1178_ = lean_array_size(v_fst_1172_);
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_1178_, v___x_1179_, v_fst_1172_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; size_t v_sz_1182_; lean_object* v___x_1183_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v_sz_1182_ = lean_array_size(v_snd_1173_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_1182_, v___x_1179_, v_snd_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1193_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1188_ = l_Array_append___redArg(v_a_1181_, v_a_1184_);
lean_dec(v_a_1184_);
v___x_1189_ = l_Lean_Doc_joinBlocks(v___x_1188_);
lean_dec_ref(v___x_1188_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1189_);
v___x_1191_ = v___x_1186_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_a_1181_);
v_a_1194_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1183_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1183_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_snd_1173_);
v_a_1202_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1180_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1180_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1172_ = stack[0].m_obj;
lean_object* v_snd_1173_ = stack[1].m_obj;
lean_object* v___y_1174_ = stack[2].m_obj;
lean_object* v___y_1175_ = stack[3].m_obj;
lean_object* v___y_1176_ = stack[4].m_obj;
lean_object* v_res_1210_;
v_res_1210_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(v_fst_1172_, v_snd_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
stack->m_obj
 = v_res_1210_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed(lean_object* v_fst_1211_, lean_object* v_snd_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(v_fst_1211_, v_snd_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
return v_res_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
lean_ctor_set(v___x_1224_, 2, v___x_1223_);
lean_ctor_set(v___x_1224_, 3, v___x_1223_);
lean_ctor_set(v___x_1224_, 4, v___x_1222_);
lean_ctor_set(v___x_1224_, 5, v___x_1222_);
lean_ctor_set(v___x_1224_, 6, v___x_1222_);
lean_ctor_set(v___x_1224_, 7, v___x_1222_);
lean_ctor_set(v___x_1224_, 8, v___x_1222_);
lean_ctor_set(v___x_1224_, 9, v___x_1222_);
lean_ctor_set(v___x_1224_, 10, v___x_1222_);
lean_ctor_set(v___x_1224_, 11, v___x_1221_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(32u);
v___x_1226_ = lean_mk_empty_array_with_capacity(v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1228_ = ((size_t)5ULL);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_unsigned_to_nat(32u);
v___x_1231_ = lean_mk_empty_array_with_capacity(v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3);
v___x_1233_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1231_);
lean_ctor_set(v___x_1233_, 2, v___x_1229_);
lean_ctor_set(v___x_1233_, 3, v___x_1229_);
lean_ctor_set_usize(v___x_1233_, 4, v___x_1228_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = lean_box(1);
v___x_1235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_1236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___x_1235_);
lean_ctor_set(v___x_1237_, 2, v___x_1234_);
return v___x_1237_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_msgData_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_env_1242_; uint8_t v___x_1243_; lean_object* v_env_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_scopes_1247_; lean_object* v___x_1248_; lean_object* v_opts_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1241_ = lean_st_ref_get(v___y_1239_);
v_env_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_env_1242_);
lean_dec(v___x_1241_);
v___x_1243_ = 0;
v_env_1244_ = l_Lean_Environment_setRecordingDeps(v_env_1242_, v___x_1243_);
v___x_1245_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1246_ = lean_st_ref_get(v___y_1239_);
v_scopes_1247_ = lean_ctor_get(v___x_1246_, 2);
lean_inc(v_scopes_1247_);
lean_dec(v___x_1246_);
v___x_1248_ = l_List_head_x21___redArg(v___x_1245_, v_scopes_1247_);
lean_dec(v_scopes_1247_);
v_opts_1249_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_opts_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2);
v___x_1251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5);
v___x_1252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1252_, 0, v_env_1244_);
lean_ctor_set(v___x_1252_, 1, v___x_1250_);
lean_ctor_set(v___x_1252_, 2, v___x_1251_);
lean_ctor_set(v___x_1252_, 3, v_opts_1249_);
v___x_1253_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_msgData_1238_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1238_ = stack[0].m_obj;
lean_object* v___y_1239_ = stack[1].m_obj;
lean_object* v_res_1255_;
v_res_1255_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1238_, v___y_1239_);
stack->m_obj
 = v_res_1255_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_msgData_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1256_, v___y_1257_);
lean_dec(v___y_1257_);
return v_res_1259_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_box(1);
v___x_1261_ = l_Lean_MessageData_ofFormat(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__2));
v___x_1266_ = l_Lean_MessageData_ofFormat(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
return v_x_1267_;
}
else
{
lean_object* v_head_1269_; lean_object* v_tail_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1292_; 
v_head_1269_ = lean_ctor_get(v_x_1268_, 0);
v_tail_1270_ = lean_ctor_get(v_x_1268_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1272_ = v_x_1268_;
v_isShared_1273_ = v_isSharedCheck_1292_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_tail_1270_);
lean_inc(v_head_1269_);
lean_dec(v_x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1292_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_before_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1290_; 
v_before_1274_ = lean_ctor_get(v_head_1269_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_head_1269_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_head_1269_, 1);
lean_dec(v_unused_1291_);
v___x_1276_ = v_head_1269_;
v_isShared_1277_ = v_isSharedCheck_1290_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_before_1274_);
lean_dec(v_head_1269_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1290_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 7);
lean_ctor_set(v___x_1276_, 1, v___x_1278_);
lean_ctor_set(v___x_1276_, 0, v_x_1267_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_x_1267_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__3);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 7);
lean_ctor_set(v___x_1272_, 1, v___x_1281_);
lean_ctor_set(v___x_1272_, 0, v___x_1280_);
v___x_1283_ = v___x_1272_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = l_Lean_MessageData_ofSyntax(v_before_1274_);
v___x_1285_ = l_Lean_indentD(v___x_1284_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1283_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v_x_1267_ = v___x_1286_;
v_x_1268_ = v_tail_1270_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(lean_object* v_opts_1293_, lean_object* v_opt_1294_){
_start:
{
lean_object* v_name_1295_; lean_object* v_defValue_1296_; lean_object* v_map_1297_; lean_object* v___x_1298_; 
v_name_1295_ = lean_ctor_get(v_opt_1294_, 0);
v_defValue_1296_ = lean_ctor_get(v_opt_1294_, 1);
v_map_1297_ = lean_ctor_get(v_opts_1293_, 0);
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1297_, v_name_1295_);
if (lean_obj_tag(v___x_1298_) == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_unbox(v_defValue_1296_);
return v___x_1299_;
}
else
{
lean_object* v_val_1300_; 
v_val_1300_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1300_);
lean_dec_ref_known(v___x_1298_, 1);
if (lean_obj_tag(v_val_1300_) == 1)
{
uint8_t v_v_1301_; 
v_v_1301_ = lean_ctor_get_uint8(v_val_1300_, 0);
lean_dec_ref_known(v_val_1300_, 0);
return v_v_1301_;
}
else
{
uint8_t v___x_1302_; 
lean_dec(v_val_1300_);
v___x_1302_ = lean_unbox(v_defValue_1296_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1293_ = stack[0].m_obj;
lean_object* v_opt_1294_ = stack[1].m_obj;
uint8_t v_res_1303_;
v_res_1303_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1293_, v_opt_1294_);
stack->m_num = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17___boxed(lean_object* v_opts_1304_, lean_object* v_opt_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1304_, v_opt_1305_);
lean_dec_ref(v_opt_1305_);
lean_dec_ref(v_opts_1304_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__1));
v___x_1312_ = l_Lean_MessageData_ofFormat(v___x_1311_);
return v___x_1312_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_msgData_1313_, lean_object* v_macroStack_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_scopes_1319_; lean_object* v___x_1320_; lean_object* v_opts_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1317_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1318_ = lean_st_ref_get(v___y_1315_);
v_scopes_1319_ = lean_ctor_get(v___x_1318_, 2);
lean_inc(v_scopes_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = l_List_head_x21___redArg(v___x_1317_, v_scopes_1319_);
lean_dec(v_scopes_1319_);
v_opts_1321_ = lean_ctor_get(v___x_1320_, 1);
lean_inc_ref(v_opts_1321_);
lean_dec(v___x_1320_);
v___x_1322_ = l_Lean_Elab_pp_macroStack;
v___x_1323_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_1321_, v___x_1322_);
lean_dec_ref(v_opts_1321_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_macroStack_1314_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_msgData_1313_);
return v___x_1324_;
}
else
{
if (lean_obj_tag(v_macroStack_1314_) == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_msgData_1313_);
return v___x_1325_;
}
else
{
lean_object* v_head_1326_; lean_object* v_after_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1342_; 
v_head_1326_ = lean_ctor_get(v_macroStack_1314_, 0);
lean_inc(v_head_1326_);
v_after_1327_ = lean_ctor_get(v_head_1326_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_head_1326_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_head_1326_, 0);
lean_dec(v_unused_1343_);
v___x_1329_ = v_head_1326_;
v_isShared_1330_ = v_isSharedCheck_1342_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_after_1327_);
lean_dec(v_head_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1342_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 7);
lean_ctor_set(v___x_1329_, 1, v___x_1331_);
lean_ctor_set(v___x_1329_, 0, v_msgData_1313_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_msgData_1313_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_msgData_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1334_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___closed__2);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = l_Lean_MessageData_ofSyntax(v_after_1327_);
v___x_1337_ = l_Lean_indentD(v___x_1336_);
v_msgData_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1338_, 0, v___x_1335_);
lean_ctor_set(v_msgData_1338_, 1, v___x_1337_);
v___x_1339_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18(v_msgData_1338_, v_macroStack_1314_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1313_ = stack[0].m_obj;
lean_object* v_macroStack_1314_ = stack[1].m_obj;
lean_object* v___y_1315_ = stack[2].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1313_, v_macroStack_1314_, v___y_1315_);
stack->m_obj
 = v_res_1344_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_msgData_1345_, lean_object* v_macroStack_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1345_, v_macroStack_1346_, v___y_1347_);
lean_dec(v___y_1347_);
return v_res_1349_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Elab_Command_getRef___redArg(v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_macroStack_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v_macroStack_1356_ = lean_ctor_get(v___y_1351_, 4);
v___x_1357_ = l_Lean_Elab_getBetterRef(v_a_1355_, v_macroStack_1356_);
lean_dec(v_a_1355_);
v___x_1358_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msg_1350_, v___y_1352_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref(v___x_1358_);
lean_inc(v_macroStack_1356_);
v___x_1360_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_a_1359_, v_macroStack_1356_, v___y_1352_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1357_);
lean_ctor_set(v___x_1365_, 1, v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 1);
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_msg_1350_);
v_a_1370_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1354_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1354_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1350_ = stack[0].m_obj;
lean_object* v___y_1351_ = stack[1].m_obj;
lean_object* v___y_1352_ = stack[2].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1350_, v___y_1351_, v___y_1352_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1383_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object* v_ref_1384_, lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Elab_Command_getRef___redArg(v___y_1386_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v_fileName_1391_; lean_object* v_fileMap_1392_; lean_object* v_currRecDepth_1393_; lean_object* v_cmdPos_1394_; lean_object* v_macroStack_1395_; lean_object* v_quotContext_x3f_1396_; lean_object* v_currMacroScope_1397_; lean_object* v_snap_x3f_1398_; lean_object* v_cancelTk_x3f_1399_; uint8_t v_suppressElabErrors_1400_; lean_object* v_ref_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v_fileName_1391_ = lean_ctor_get(v___y_1386_, 0);
v_fileMap_1392_ = lean_ctor_get(v___y_1386_, 1);
v_currRecDepth_1393_ = lean_ctor_get(v___y_1386_, 2);
v_cmdPos_1394_ = lean_ctor_get(v___y_1386_, 3);
v_macroStack_1395_ = lean_ctor_get(v___y_1386_, 4);
v_quotContext_x3f_1396_ = lean_ctor_get(v___y_1386_, 5);
v_currMacroScope_1397_ = lean_ctor_get(v___y_1386_, 6);
v_snap_x3f_1398_ = lean_ctor_get(v___y_1386_, 8);
v_cancelTk_x3f_1399_ = lean_ctor_get(v___y_1386_, 9);
v_suppressElabErrors_1400_ = lean_ctor_get_uint8(v___y_1386_, sizeof(void*)*10);
v_ref_1401_ = l_Lean_replaceRef(v_ref_1384_, v_a_1390_);
lean_dec(v_a_1390_);
lean_inc(v_cancelTk_x3f_1399_);
lean_inc(v_snap_x3f_1398_);
lean_inc(v_currMacroScope_1397_);
lean_inc(v_quotContext_x3f_1396_);
lean_inc(v_macroStack_1395_);
lean_inc(v_cmdPos_1394_);
lean_inc(v_currRecDepth_1393_);
lean_inc_ref(v_fileMap_1392_);
lean_inc_ref(v_fileName_1391_);
v___x_1402_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1402_, 0, v_fileName_1391_);
lean_ctor_set(v___x_1402_, 1, v_fileMap_1392_);
lean_ctor_set(v___x_1402_, 2, v_currRecDepth_1393_);
lean_ctor_set(v___x_1402_, 3, v_cmdPos_1394_);
lean_ctor_set(v___x_1402_, 4, v_macroStack_1395_);
lean_ctor_set(v___x_1402_, 5, v_quotContext_x3f_1396_);
lean_ctor_set(v___x_1402_, 6, v_currMacroScope_1397_);
lean_ctor_set(v___x_1402_, 7, v_ref_1401_);
lean_ctor_set(v___x_1402_, 8, v_snap_x3f_1398_);
lean_ctor_set(v___x_1402_, 9, v_cancelTk_x3f_1399_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*10, v_suppressElabErrors_1400_);
v___x_1403_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1385_, v___x_1402_, v___y_1387_);
lean_dec_ref_known(v___x_1402_, 10);
return v___x_1403_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_msg_1385_);
v_a_1404_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1389_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1389_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1384_ = stack[0].m_obj;
lean_object* v_msg_1385_ = stack[1].m_obj;
lean_object* v___y_1386_ = stack[2].m_obj;
lean_object* v___y_1387_ = stack[3].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1384_, v_msg_1385_, v___y_1386_, v___y_1387_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object* v_ref_1413_, lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1413_, v_msg_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v_ref_1413_);
return v_res_1418_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0));
v___x_1421_ = l_Lean_stringToMessageData(v___x_1420_);
return v___x_1421_;
}
}
lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object* v_stx_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = l_Lean_Syntax_getArg(v_stx_1426_, v___x_1436_);
if (lean_obj_tag(v___x_1437_) == 1)
{
lean_object* v_kind_1438_; 
v_kind_1438_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_kind_1438_);
if (lean_obj_tag(v_kind_1438_) == 1)
{
lean_object* v_pre_1439_; 
v_pre_1439_ = lean_ctor_get(v_kind_1438_, 0);
lean_inc(v_pre_1439_);
if (lean_obj_tag(v_pre_1439_) == 1)
{
lean_object* v_pre_1440_; 
v_pre_1440_ = lean_ctor_get(v_pre_1439_, 0);
lean_inc(v_pre_1440_);
if (lean_obj_tag(v_pre_1440_) == 1)
{
lean_object* v_pre_1441_; 
v_pre_1441_ = lean_ctor_get(v_pre_1440_, 0);
lean_inc(v_pre_1441_);
if (lean_obj_tag(v_pre_1441_) == 1)
{
lean_object* v_pre_1442_; 
v_pre_1442_ = lean_ctor_get(v_pre_1441_, 0);
if (lean_obj_tag(v_pre_1442_) == 0)
{
lean_object* v_args_1443_; lean_object* v_str_1444_; lean_object* v_str_1445_; lean_object* v_str_1446_; lean_object* v_str_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_args_1443_ = lean_ctor_get(v___x_1437_, 2);
lean_inc_ref(v_args_1443_);
lean_dec_ref_known(v___x_1437_, 3);
v_str_1444_ = lean_ctor_get(v_kind_1438_, 1);
lean_inc_ref(v_str_1444_);
lean_dec_ref_known(v_kind_1438_, 2);
v_str_1445_ = lean_ctor_get(v_pre_1439_, 1);
lean_inc_ref(v_str_1445_);
lean_dec_ref_known(v_pre_1439_, 2);
v_str_1446_ = lean_ctor_get(v_pre_1440_, 1);
lean_inc_ref(v_str_1446_);
lean_dec_ref_known(v_pre_1440_, 2);
v_str_1447_ = lean_ctor_get(v_pre_1441_, 1);
lean_inc_ref(v_str_1447_);
lean_dec_ref_known(v_pre_1441_, 2);
v___x_1448_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2));
v___x_1449_ = lean_string_dec_eq(v_str_1447_, v___x_1448_);
lean_dec_ref(v_str_1447_);
if (v___x_1449_ == 0)
{
lean_dec_ref(v_str_1446_);
lean_dec_ref(v_str_1445_);
lean_dec_ref(v_str_1444_);
lean_dec_ref(v_args_1443_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3));
v___x_1451_ = lean_string_dec_eq(v_str_1446_, v___x_1450_);
lean_dec_ref(v_str_1446_);
if (v___x_1451_ == 0)
{
lean_dec_ref(v_str_1445_);
lean_dec_ref(v_str_1444_);
lean_dec_ref(v_args_1443_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4));
v___x_1453_ = lean_string_dec_eq(v_str_1445_, v___x_1452_);
lean_dec_ref(v_str_1445_);
if (v___x_1453_ == 0)
{
lean_dec_ref(v_str_1444_);
lean_dec_ref(v_args_1443_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5));
v___x_1455_ = lean_string_dec_eq(v_str_1444_, v___x_1454_);
lean_dec_ref(v_str_1444_);
if (v___x_1455_ == 0)
{
lean_dec_ref(v_args_1443_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = lean_array_get_size(v_args_1443_);
v___x_1457_ = lean_unsigned_to_nat(2u);
v___x_1458_ = lean_nat_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_dec_ref(v_args_1443_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_array_fget(v_args_1443_, v___x_1459_);
lean_dec_ref(v_args_1443_);
if (lean_obj_tag(v___x_1460_) == 2)
{
lean_object* v_val_1461_; lean_object* v___x_1462_; 
lean_dec(v_stx_1426_);
v_val_1461_ = lean_ctor_get(v___x_1460_, 1);
lean_inc_ref(v_val_1461_);
lean_dec_ref_known(v___x_1460_, 2);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_val_1461_);
return v___x_1462_;
}
else
{
lean_dec(v___x_1460_);
goto v___jp_1430_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1441_, 2);
lean_dec_ref_known(v_pre_1440_, 2);
lean_dec_ref_known(v_pre_1439_, 2);
lean_dec_ref_known(v_kind_1438_, 2);
lean_dec_ref_known(v___x_1437_, 3);
goto v___jp_1430_;
}
}
else
{
lean_dec_ref_known(v_pre_1440_, 2);
lean_dec(v_pre_1441_);
lean_dec_ref_known(v_pre_1439_, 2);
lean_dec_ref_known(v_kind_1438_, 2);
lean_dec_ref_known(v___x_1437_, 3);
goto v___jp_1430_;
}
}
else
{
lean_dec_ref_known(v_pre_1439_, 2);
lean_dec(v_pre_1440_);
lean_dec_ref_known(v_kind_1438_, 2);
lean_dec_ref_known(v___x_1437_, 3);
goto v___jp_1430_;
}
}
else
{
lean_dec(v_pre_1439_);
lean_dec_ref_known(v_kind_1438_, 2);
lean_dec_ref_known(v___x_1437_, 3);
goto v___jp_1430_;
}
}
else
{
lean_dec_ref_known(v___x_1437_, 3);
lean_dec(v_kind_1438_);
goto v___jp_1430_;
}
}
else
{
lean_dec(v___x_1437_);
goto v___jp_1430_;
}
v___jp_1430_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1431_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1);
lean_inc(v_stx_1426_);
v___x_1432_ = l_Lean_MessageData_ofSyntax(v_stx_1426_);
v___x_1433_ = l_Lean_indentD(v___x_1432_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1431_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_stx_1426_, v___x_1434_, v___y_1427_, v___y_1428_);
lean_dec(v_stx_1426_);
return v___x_1435_;
}
}
}
LEAN_EXPORT void l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1426_ = stack[0].m_obj;
lean_object* v___y_1427_ = stack[1].m_obj;
lean_object* v___y_1428_ = stack[2].m_obj;
lean_object* v_res_1463_;
v_res_1463_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_stx_1426_, v___y_1427_, v___y_1428_);
stack->m_obj
 = v_res_1463_;
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object* v_stx_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_stx_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1468_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object* v_doc_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = l_Lean_isVersoDocComment(v_doc_1469_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_doc_1469_, v_a_1470_, v_a_1471_);
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___boxed), 4, 1);
lean_closure_set(v___x_1475_, 0, v_doc_1469_);
v___x_1476_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1475_, v_a_1470_, v_a_1471_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1507_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1507_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1507_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
if (lean_obj_tag(v_a_1477_) == 1)
{
lean_object* v_val_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_del_object(v___x_1479_);
v_val_1481_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v_a_1477_, 1);
v___x_1482_ = l_Lean_TSyntax_getVersoBlocks(v_val_1481_);
lean_dec(v_val_1481_);
v___x_1483_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1483_, 0, v___x_1482_);
v___x_1484_ = 0;
v___x_1485_ = lean_box(v___x_1484_);
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_Doc_DocM_execForModule___boxed), 10, 3);
lean_closure_set(v___x_1486_, 0, lean_box(0));
lean_closure_set(v___x_1486_, 1, v___x_1483_);
lean_closure_set(v___x_1486_, 2, v___x_1485_);
v___x_1487_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1486_, v_a_1470_, v_a_1471_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v_fst_1489_; lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v_fst_1489_ = lean_ctor_get(v_a_1488_, 0);
lean_inc(v_fst_1489_);
lean_dec(v_a_1488_);
v_fst_1490_ = lean_ctor_get(v_fst_1489_, 0);
lean_inc(v_fst_1490_);
v_snd_1491_ = lean_ctor_get(v_fst_1489_, 1);
lean_inc(v_snd_1491_);
lean_dec(v_fst_1489_);
v___f_1492_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1492_, 0, v_fst_1490_);
lean_closure_set(v___f_1492_, 1, v_snd_1491_);
v___x_1493_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_1493_, 0, v___f_1492_);
v___x_1494_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1493_, v_a_1470_, v_a_1471_);
return v___x_1494_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1487_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1487_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
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
else
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v_a_1477_);
v___x_1503_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1503_);
v___x_1505_ = v___x_1479_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1476_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1476_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_1469_ = stack[0].m_obj;
lean_object* v_a_1470_ = stack[1].m_obj;
lean_object* v_a_1471_ = stack[2].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_doc_1469_, v_a_1470_, v_a_1471_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object* v_doc_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_doc_1517_, v_a_1518_, v_a_1519_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
return v_res_1521_;
}
}
lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object* v_p_1522_, lean_object* v_level_1523_, lean_object* v_part_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1523_, v_part_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT void l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_1523_ = stack[1].m_obj;
lean_object* v_part_1524_ = stack[2].m_obj;
lean_object* v_a_1525_ = stack[3].m_obj;
lean_object* v_a_1526_ = stack[4].m_obj;
lean_object* v_a_1527_ = stack[5].m_obj;
lean_object* v_res_1530_;
v_res_1530_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_box(0), v_level_1523_, v_part_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
stack->m_obj
 = v_res_1530_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object* v_p_1531_, lean_object* v_level_1532_, lean_object* v_part_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(v_p_1531_, v_level_1532_, v_part_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec(v_level_1532_);
return v_res_1538_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object* v_00_u03b1_1539_, lean_object* v_ref_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1540_, v_msg_1541_, v___y_1542_, v___y_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1540_ = stack[1].m_obj;
lean_object* v_msg_1541_ = stack[2].m_obj;
lean_object* v___y_1542_ = stack[3].m_obj;
lean_object* v___y_1543_ = stack[4].m_obj;
lean_object* v_res_1546_;
v_res_1546_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_box(0), v_ref_1540_, v_msg_1541_, v___y_1542_, v___y_1543_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_ref_1548_, lean_object* v_msg_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(v_00_u03b1_1547_, v_ref_1548_, v_msg_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v_ref_1548_);
return v_res_1553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(lean_object* v_p_1554_, lean_object* v___x_1555_, size_t v_sz_1556_, size_t v_i_1557_, lean_object* v_bs_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1555_, v_sz_1556_, v_i_1557_, v_bs_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1555_ = stack[1].m_obj;
size_t v_sz_1556_ = stack[2].m_num;
size_t v_i_1557_ = stack[3].m_num;
lean_object* v_bs_1558_ = stack[4].m_obj;
lean_object* v___y_1559_ = stack[5].m_obj;
lean_object* v___y_1560_ = stack[6].m_obj;
lean_object* v___y_1561_ = stack[7].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(lean_box(0), v___x_1555_, v_sz_1556_, v_i_1557_, v_bs_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
stack->m_obj
 = v_res_1564_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___boxed(lean_object* v_p_1565_, lean_object* v___x_1566_, lean_object* v_sz_1567_, lean_object* v_i_1568_, lean_object* v_bs_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
size_t v_sz_boxed_1574_; size_t v_i_boxed_1575_; lean_object* v_res_1576_; 
v_sz_boxed_1574_ = lean_unbox_usize(v_sz_1567_);
lean_dec(v_sz_1567_);
v_i_boxed_1575_ = lean_unbox_usize(v_i_1568_);
lean_dec(v_i_1568_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5(v_p_1565_, v___x_1566_, v_sz_boxed_1574_, v_i_boxed_1575_, v_bs_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___x_1566_);
return v_res_1576_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(lean_object* v_msgData_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v_msgData_1577_, v___y_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1577_ = stack[0].m_obj;
lean_object* v___y_1578_ = stack[1].m_obj;
lean_object* v___y_1579_ = stack[2].m_obj;
lean_object* v_res_1582_;
v_res_1582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(v_msgData_1577_, v___y_1578_, v___y_1579_);
stack->m_obj
 = v_res_1582_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_msgData_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6(v_msgData_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1587_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1588_, lean_object* v_msg_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v_msg_1589_, v___y_1590_, v___y_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1589_ = stack[1].m_obj;
lean_object* v___y_1590_ = stack[2].m_obj;
lean_object* v___y_1591_ = stack[3].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(lean_box(0), v_msg_1589_, v___y_1590_, v___y_1591_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1(v_00_u03b1_1595_, v_msg_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1600_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(lean_object* v_msgData_1601_, lean_object* v_macroStack_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___redArg(v_msgData_1601_, v_macroStack_1602_, v___y_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1601_ = stack[0].m_obj;
lean_object* v_macroStack_1602_ = stack[1].m_obj;
lean_object* v___y_1603_ = stack[2].m_obj;
lean_object* v___y_1604_ = stack[3].m_obj;
lean_object* v_res_1607_;
v_res_1607_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(v_msgData_1601_, v_macroStack_1602_, v___y_1603_, v___y_1604_);
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_msgData_1608_, lean_object* v_macroStack_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7(v_msgData_1608_, v_macroStack_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1614_, lean_object* v___x_1615_, lean_object* v_s_1616_){
_start:
{
lean_object* v_addEntryFn_1617_; lean_object* v_importedEntries_1618_; lean_object* v_state_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
v_addEntryFn_1617_ = lean_ctor_get(v___x_1614_, 3);
lean_inc(v_addEntryFn_1617_);
lean_dec_ref(v___x_1614_);
v_importedEntries_1618_ = lean_ctor_get(v_s_1616_, 0);
v_state_1619_ = lean_ctor_get(v_s_1616_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_s_1616_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v_s_1616_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_state_1619_);
lean_inc(v_importedEntries_1618_);
lean_dec(v_s_1616_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_state_1623_; lean_object* v___x_1625_; 
v_state_1623_ = lean_apply_2(v_addEntryFn_1617_, v_state_1619_, v___x_1615_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v_state_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_importedEntries_1618_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_state_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1628_, v___x_1629_, v___y_1634_, v___y_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1628_ = stack[0].m_obj;
lean_object* v___x_1629_ = stack[1].m_obj;
lean_object* v___y_1630_ = stack[2].m_obj;
lean_object* v___y_1631_ = stack[3].m_obj;
lean_object* v___y_1632_ = stack[4].m_obj;
lean_object* v___y_1633_ = stack[5].m_obj;
lean_object* v___y_1634_ = stack[6].m_obj;
lean_object* v___y_1635_ = stack[7].m_obj;
lean_object* v_res_1638_;
v_res_1638_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(v___x_1628_, v___x_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
stack->m_obj
 = v_res_1638_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed(lean_object* v___x_1639_, lean_object* v___x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(v___x_1639_, v___x_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1648_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6));
v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
v___x_1666_ = l_Lean_stringToMessageData(v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_messages_1684_; lean_object* v_scopes_1685_; lean_object* v_usedQuotCtxts_1686_; lean_object* v_nextMacroScope_1687_; lean_object* v_maxRecDepth_1688_; lean_object* v_ngen_1689_; lean_object* v_auxDeclNGen_1690_; lean_object* v_infoState_1691_; lean_object* v_traceState_1692_; lean_object* v_snapshotTasks_1693_; lean_object* v_prevLinterStates_1694_; lean_object* v_codeQualityEntryTasks_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
lean_inc(v_x_1679_);
v___x_1703_ = l_Lean_Syntax_isOfKind(v_x_1679_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_x_1679_);
v___x_1704_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1705_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1704_, v_a_1680_, v_a_1681_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = l_Lean_Syntax_getArg(v_x_1679_, v___x_1706_);
lean_inc(v___x_1707_);
v___x_1708_ = l_Lean_Syntax_matchesNull(v___x_1707_, v___x_1706_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1707_);
v___x_1710_ = l_Lean_Syntax_matchesNull(v___x_1707_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v___x_1707_);
lean_dec(v_x_1679_);
v___x_1711_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1712_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1711_, v_a_1680_, v_a_1681_);
return v___x_1712_;
}
else
{
lean_object* v_docs_1713_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; uint8_t v___y_1757_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1773_; 
v_docs_1713_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1706_);
lean_dec(v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_docs_1713_);
v___x_1807_ = l_Lean_Syntax_isOfKind(v_docs_1713_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_docs_1713_);
lean_dec(v_x_1679_);
v___x_1808_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1809_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1808_, v_a_1680_, v_a_1681_);
return v___x_1809_;
}
else
{
goto v___jp_1799_;
}
}
else
{
goto v___jp_1799_;
}
v___jp_1714_:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_docs_1713_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v_env_1721_; lean_object* v_messages_1722_; lean_object* v_scopes_1723_; lean_object* v_usedQuotCtxts_1724_; lean_object* v_nextMacroScope_1725_; lean_object* v_maxRecDepth_1726_; lean_object* v_ngen_1727_; lean_object* v_auxDeclNGen_1728_; lean_object* v_infoState_1729_; lean_object* v_traceState_1730_; lean_object* v_snapshotTasks_1731_; lean_object* v_prevLinterStates_1732_; lean_object* v_codeQualityEntryTasks_1733_; lean_object* v___x_1734_; lean_object* v_toEnvExtension_1735_; lean_object* v_asyncMode_1736_; uint8_t v_logWrites_1737_; lean_object* v___x_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = lean_st_ref_take(v___y_1717_);
v_env_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_ref(v_env_1721_);
v_messages_1722_ = lean_ctor_get(v___x_1720_, 1);
lean_inc_ref(v_messages_1722_);
v_scopes_1723_ = lean_ctor_get(v___x_1720_, 2);
lean_inc(v_scopes_1723_);
v_usedQuotCtxts_1724_ = lean_ctor_get(v___x_1720_, 3);
lean_inc(v_usedQuotCtxts_1724_);
v_nextMacroScope_1725_ = lean_ctor_get(v___x_1720_, 4);
lean_inc(v_nextMacroScope_1725_);
v_maxRecDepth_1726_ = lean_ctor_get(v___x_1720_, 5);
lean_inc(v_maxRecDepth_1726_);
v_ngen_1727_ = lean_ctor_get(v___x_1720_, 6);
lean_inc_ref(v_ngen_1727_);
v_auxDeclNGen_1728_ = lean_ctor_get(v___x_1720_, 7);
lean_inc_ref(v_auxDeclNGen_1728_);
v_infoState_1729_ = lean_ctor_get(v___x_1720_, 8);
lean_inc_ref(v_infoState_1729_);
v_traceState_1730_ = lean_ctor_get(v___x_1720_, 9);
lean_inc_ref(v_traceState_1730_);
v_snapshotTasks_1731_ = lean_ctor_get(v___x_1720_, 10);
lean_inc_ref(v_snapshotTasks_1731_);
v_prevLinterStates_1732_ = lean_ctor_get(v___x_1720_, 11);
lean_inc(v_prevLinterStates_1732_);
v_codeQualityEntryTasks_1733_ = lean_ctor_get(v___x_1720_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1733_);
lean_dec(v___x_1720_);
v___x_1734_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_1735_ = lean_ctor_get(v___x_1734_, 0);
v_asyncMode_1736_ = lean_ctor_get(v_toEnvExtension_1735_, 2);
v_logWrites_1737_ = lean_ctor_get_uint8(v_toEnvExtension_1735_, sizeof(void*)*6);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___y_1715_);
lean_ctor_set(v___x_1738_, 1, v_a_1719_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0), 3, 2);
lean_closure_set(v___f_1739_, 0, v___x_1734_);
lean_closure_set(v___f_1739_, 1, v___x_1738_);
v___x_1740_ = lean_box(0);
if (v_logWrites_1737_ == 0)
{
lean_object* v___x_1741_; 
lean_inc_ref(v_toEnvExtension_1735_);
v___x_1741_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1735_, v_env_1721_, v___f_1739_, v_asyncMode_1736_, v___x_1740_, v___x_1710_);
v_messages_1684_ = v_messages_1722_;
v_scopes_1685_ = v_scopes_1723_;
v_usedQuotCtxts_1686_ = v_usedQuotCtxts_1724_;
v_nextMacroScope_1687_ = v_nextMacroScope_1725_;
v_maxRecDepth_1688_ = v_maxRecDepth_1726_;
v_ngen_1689_ = v_ngen_1727_;
v_auxDeclNGen_1690_ = v_auxDeclNGen_1728_;
v_infoState_1691_ = v_infoState_1729_;
v_traceState_1692_ = v_traceState_1730_;
v_snapshotTasks_1693_ = v_snapshotTasks_1731_;
v_prevLinterStates_1694_ = v_prevLinterStates_1732_;
v_codeQualityEntryTasks_1695_ = v_codeQualityEntryTasks_1733_;
v___y_1696_ = v___y_1717_;
v___y_1697_ = v___x_1741_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc_ref_n(v_toEnvExtension_1735_, 2);
v___x_1742_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1735_, v_env_1721_);
lean_dec_ref(v_env_1721_);
v___x_1743_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1735_, v___x_1742_, v___f_1739_, v_asyncMode_1736_, v___x_1740_, v___x_1710_);
v_messages_1684_ = v_messages_1722_;
v_scopes_1685_ = v_scopes_1723_;
v_usedQuotCtxts_1686_ = v_usedQuotCtxts_1724_;
v_nextMacroScope_1687_ = v_nextMacroScope_1725_;
v_maxRecDepth_1688_ = v_maxRecDepth_1726_;
v_ngen_1689_ = v_ngen_1727_;
v_auxDeclNGen_1690_ = v_auxDeclNGen_1728_;
v_infoState_1691_ = v_infoState_1729_;
v_traceState_1692_ = v_traceState_1730_;
v_snapshotTasks_1693_ = v_snapshotTasks_1731_;
v_prevLinterStates_1694_ = v_prevLinterStates_1732_;
v_codeQualityEntryTasks_1695_ = v_codeQualityEntryTasks_1733_;
v___y_1696_ = v___y_1717_;
v___y_1697_ = v___x_1743_;
goto v___jp_1683_;
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v___y_1715_);
v_a_1744_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1718_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1718_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
v___jp_1752_:
{
if (v___y_1757_ == 0)
{
lean_dec(v___y_1754_);
v___y_1715_ = v___y_1755_;
v___y_1716_ = v___y_1753_;
v___y_1717_ = v___y_1756_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_docs_1713_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1759_ = l_Lean_MessageData_ofConstName(v___y_1755_, v___x_1708_);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1754_, v___x_1762_, v___y_1753_, v___y_1756_);
lean_dec(v___y_1754_);
return v___x_1763_;
}
}
v___jp_1764_:
{
lean_object* v___x_1769_; lean_object* v_env_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_st_ref_get(v___y_1768_);
v_env_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc_ref(v_env_1770_);
lean_dec(v___x_1769_);
v___x_1771_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1770_, v___y_1766_);
if (v___x_1771_ == 0)
{
v___y_1753_ = v___y_1767_;
v___y_1754_ = v___y_1765_;
v___y_1755_ = v___y_1766_;
v___y_1756_ = v___y_1768_;
v___y_1757_ = v___x_1710_;
goto v___jp_1752_;
}
else
{
v___y_1753_ = v___y_1767_;
v___y_1754_ = v___y_1765_;
v___y_1755_ = v___y_1766_;
v___y_1756_ = v___y_1768_;
v___y_1757_ = v___x_1708_;
goto v___jp_1752_;
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___f_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(0);
lean_inc(v___y_1773_);
v___f_1775_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1775_, 0, v___y_1773_);
lean_closure_set(v___f_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1775_, v_a_1680_, v_a_1681_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v_env_1779_; lean_object* v___x_1780_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_n(v_a_1777_, 2);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = lean_st_ref_get(v_a_1681_);
v_env_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc_ref(v_env_1779_);
lean_dec(v___x_1778_);
v___x_1780_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1779_, v_a_1777_);
if (lean_obj_tag(v___x_1780_) == 1)
{
lean_object* v_val_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_docs_1713_);
v_val_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_1783_ = l_Lean_MessageData_ofConstName(v_a_1777_, v___x_1708_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_MessageData_ofConstName(v_val_1781_, v___x_1708_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1782_);
v___x_1790_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_1773_, v___x_1789_, v_a_1680_, v_a_1681_);
lean_dec(v___y_1773_);
return v___x_1790_;
}
else
{
lean_dec(v___x_1780_);
v___y_1765_ = v___y_1773_;
v___y_1766_ = v_a_1777_;
v___y_1767_ = v_a_1680_;
v___y_1768_ = v_a_1681_;
goto v___jp_1764_;
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v___y_1773_);
lean_dec(v_docs_1713_);
v_a_1791_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1776_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1776_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(2u);
v___x_1801_ = l_Lean_Syntax_getArg(v_x_1679_, v___x_1800_);
lean_dec(v_x_1679_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v___x_1801_);
v___x_1803_ = l_Lean_Syntax_isOfKind(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v___x_1801_);
lean_dec(v_docs_1713_);
v___x_1804_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1805_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1804_, v_a_1680_, v_a_1681_);
return v___x_1805_;
}
else
{
v___y_1773_ = v___x_1801_;
goto v___jp_1772_;
}
}
else
{
v___y_1773_ = v___x_1801_;
goto v___jp_1772_;
}
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v_cmd_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v___x_1707_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v_cmd_1811_ = l_Lean_Syntax_getArg(v_x_1679_, v___x_1810_);
lean_dec(v_x_1679_);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15);
v___x_1813_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_cmd_1811_, v___x_1812_, v_a_1680_, v_a_1681_);
lean_dec(v_cmd_1811_);
return v___x_1813_;
}
}
v___jp_1683_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1698_, 0, v___y_1697_);
lean_ctor_set(v___x_1698_, 1, v_messages_1684_);
lean_ctor_set(v___x_1698_, 2, v_scopes_1685_);
lean_ctor_set(v___x_1698_, 3, v_usedQuotCtxts_1686_);
lean_ctor_set(v___x_1698_, 4, v_nextMacroScope_1687_);
lean_ctor_set(v___x_1698_, 5, v_maxRecDepth_1688_);
lean_ctor_set(v___x_1698_, 6, v_ngen_1689_);
lean_ctor_set(v___x_1698_, 7, v_auxDeclNGen_1690_);
lean_ctor_set(v___x_1698_, 8, v_infoState_1691_);
lean_ctor_set(v___x_1698_, 9, v_traceState_1692_);
lean_ctor_set(v___x_1698_, 10, v_snapshotTasks_1693_);
lean_ctor_set(v___x_1698_, 11, v_prevLinterStates_1694_);
lean_ctor_set(v___x_1698_, 12, v_codeQualityEntryTasks_1695_);
v___x_1699_ = lean_st_ref_put(v___y_1696_, v___x_1698_);
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
return v___x_1701_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_elabTacticExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1679_ = stack[0].m_obj;
lean_object* v_a_1680_ = stack[1].m_obj;
lean_object* v_a_1681_ = stack[2].m_obj;
lean_object* v_res_1814_;
v_res_1814_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_1679_, v_a_1680_, v_a_1681_);
stack->m_obj
 = v_res_1814_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1819_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1831_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_1833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1834_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_1835_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1831_, v___x_1832_, v___x_1833_, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1836_;
v_res_1836_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
stack->m_obj
 = v_res_1836_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_1838_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_1867_ = l_Lean_addBuiltinDeclarationRanges(v___x_1865_, v___x_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1868_;
v_res_1868_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
stack->m_obj
 = v_res_1868_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0(lean_object* v___x_1871_, lean_object* v___x_1872_, lean_object* v_s_1873_){
_start:
{
lean_object* v_addEntryFn_1874_; lean_object* v_importedEntries_1875_; lean_object* v_state_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1884_; 
v_addEntryFn_1874_ = lean_ctor_get(v___x_1871_, 3);
lean_inc(v_addEntryFn_1874_);
lean_dec_ref(v___x_1871_);
v_importedEntries_1875_ = lean_ctor_get(v_s_1873_, 0);
v_state_1876_ = lean_ctor_get(v_s_1873_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_s_1873_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1878_ = v_s_1873_;
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_state_1876_);
lean_inc(v_importedEntries_1875_);
lean_dec(v_s_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_state_1880_; lean_object* v___x_1882_; 
v_state_1880_ = lean_apply_2(v_addEntryFn_1874_, v_state_1876_, v___x_1872_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_state_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_importedEntries_1875_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_state_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2));
v___x_1893_ = l_Lean_stringToMessageData(v___x_1892_);
return v___x_1893_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_messages_1904_; lean_object* v_scopes_1905_; lean_object* v_usedQuotCtxts_1906_; lean_object* v_nextMacroScope_1907_; lean_object* v_maxRecDepth_1908_; lean_object* v_ngen_1909_; lean_object* v_auxDeclNGen_1910_; lean_object* v_infoState_1911_; lean_object* v_traceState_1912_; lean_object* v_snapshotTasks_1913_; lean_object* v_prevLinterStates_1914_; lean_object* v_codeQualityEntryTasks_1915_; lean_object* v___y_1916_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v_a_1926_; lean_object* v_doc_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; 
v___x_1920_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
lean_inc(v_x_1897_);
v___x_1921_ = l_Lean_Syntax_isOfKind(v_x_1897_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_x_1897_);
v___x_1990_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1991_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1990_, v_a_1898_, v_a_1899_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = l_Lean_Syntax_getArg(v_x_1897_, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_isNone(v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1993_);
v___x_1996_ = l_Lean_Syntax_matchesNull(v___x_1993_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec(v___x_1993_);
lean_dec(v_x_1897_);
v___x_1997_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1998_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1997_, v_a_1898_, v_a_1899_);
return v___x_1998_;
}
else
{
lean_object* v_doc_1999_; 
v_doc_1999_ = l_Lean_Syntax_getArg(v___x_1993_, v___x_1992_);
lean_dec(v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_doc_1999_);
v___x_2003_ = l_Lean_Syntax_isOfKind(v_doc_1999_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec(v_doc_1999_);
lean_dec(v_x_1897_);
v___x_2004_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_2005_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_2004_, v_a_1898_, v_a_1899_);
return v___x_2005_;
}
else
{
goto v___jp_2000_;
}
}
else
{
goto v___jp_2000_;
}
v___jp_2000_:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_doc_1999_);
v_doc_1956_ = v___x_2001_;
v___y_1957_ = v_a_1898_;
v___y_1958_ = v_a_1899_;
goto v___jp_1955_;
}
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v___x_1993_);
v___x_2006_ = lean_box(0);
v_doc_1956_ = v___x_2006_;
v___y_1957_ = v_a_1898_;
v___y_1958_ = v_a_1899_;
goto v___jp_1955_;
}
}
v___jp_1901_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1917_, 0, v___y_1916_);
lean_ctor_set(v___x_1917_, 1, v_messages_1904_);
lean_ctor_set(v___x_1917_, 2, v_scopes_1905_);
lean_ctor_set(v___x_1917_, 3, v_usedQuotCtxts_1906_);
lean_ctor_set(v___x_1917_, 4, v_nextMacroScope_1907_);
lean_ctor_set(v___x_1917_, 5, v_maxRecDepth_1908_);
lean_ctor_set(v___x_1917_, 6, v_ngen_1909_);
lean_ctor_set(v___x_1917_, 7, v_auxDeclNGen_1910_);
lean_ctor_set(v___x_1917_, 8, v_infoState_1911_);
lean_ctor_set(v___x_1917_, 9, v_traceState_1912_);
lean_ctor_set(v___x_1917_, 10, v_snapshotTasks_1913_);
lean_ctor_set(v___x_1917_, 11, v_prevLinterStates_1914_);
lean_ctor_set(v___x_1917_, 12, v_codeQualityEntryTasks_1915_);
v___x_1918_ = lean_st_ref_put(v___y_1903_, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___y_1902_);
return v___x_1919_;
}
v___jp_1922_:
{
lean_object* v___x_1927_; lean_object* v_env_1928_; lean_object* v_messages_1929_; lean_object* v_scopes_1930_; lean_object* v_usedQuotCtxts_1931_; lean_object* v_nextMacroScope_1932_; lean_object* v_maxRecDepth_1933_; lean_object* v_ngen_1934_; lean_object* v_auxDeclNGen_1935_; lean_object* v_infoState_1936_; lean_object* v_traceState_1937_; lean_object* v_snapshotTasks_1938_; lean_object* v_prevLinterStates_1939_; lean_object* v_codeQualityEntryTasks_1940_; lean_object* v___x_1941_; lean_object* v_toEnvExtension_1942_; lean_object* v_asyncMode_1943_; uint8_t v_logWrites_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; 
v___x_1927_ = lean_st_ref_take(v___y_1925_);
v_env_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_ref(v_env_1928_);
v_messages_1929_ = lean_ctor_get(v___x_1927_, 1);
lean_inc_ref(v_messages_1929_);
v_scopes_1930_ = lean_ctor_get(v___x_1927_, 2);
lean_inc(v_scopes_1930_);
v_usedQuotCtxts_1931_ = lean_ctor_get(v___x_1927_, 3);
lean_inc(v_usedQuotCtxts_1931_);
v_nextMacroScope_1932_ = lean_ctor_get(v___x_1927_, 4);
lean_inc(v_nextMacroScope_1932_);
v_maxRecDepth_1933_ = lean_ctor_get(v___x_1927_, 5);
lean_inc(v_maxRecDepth_1933_);
v_ngen_1934_ = lean_ctor_get(v___x_1927_, 6);
lean_inc_ref(v_ngen_1934_);
v_auxDeclNGen_1935_ = lean_ctor_get(v___x_1927_, 7);
lean_inc_ref(v_auxDeclNGen_1935_);
v_infoState_1936_ = lean_ctor_get(v___x_1927_, 8);
lean_inc_ref(v_infoState_1936_);
v_traceState_1937_ = lean_ctor_get(v___x_1927_, 9);
lean_inc_ref(v_traceState_1937_);
v_snapshotTasks_1938_ = lean_ctor_get(v___x_1927_, 10);
lean_inc_ref(v_snapshotTasks_1938_);
v_prevLinterStates_1939_ = lean_ctor_get(v___x_1927_, 11);
lean_inc(v_prevLinterStates_1939_);
v_codeQualityEntryTasks_1940_ = lean_ctor_get(v___x_1927_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1940_);
lean_dec(v___x_1927_);
v___x_1941_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1942_ = lean_ctor_get(v___x_1941_, 0);
v_asyncMode_1943_ = lean_ctor_get(v_toEnvExtension_1942_, 2);
v_logWrites_1944_ = lean_ctor_get_uint8(v_toEnvExtension_1942_, sizeof(void*)*6);
v___x_1945_ = lean_box(0);
v___x_1946_ = l_Lean_TSyntax_getId(v___y_1924_);
lean_dec(v___y_1924_);
v___x_1947_ = l_Lean_TSyntax_getString(v___y_1923_);
lean_dec(v___y_1923_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v_a_1926_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0), 3, 2);
lean_closure_set(v___f_1950_, 0, v___x_1941_);
lean_closure_set(v___f_1950_, 1, v___x_1949_);
v___x_1951_ = lean_box(0);
if (v_logWrites_1944_ == 0)
{
lean_object* v___x_1952_; 
lean_inc_ref(v_toEnvExtension_1942_);
v___x_1952_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1942_, v_env_1928_, v___f_1950_, v_asyncMode_1943_, v___x_1951_, v___x_1921_);
v___y_1902_ = v___x_1945_;
v___y_1903_ = v___y_1925_;
v_messages_1904_ = v_messages_1929_;
v_scopes_1905_ = v_scopes_1930_;
v_usedQuotCtxts_1906_ = v_usedQuotCtxts_1931_;
v_nextMacroScope_1907_ = v_nextMacroScope_1932_;
v_maxRecDepth_1908_ = v_maxRecDepth_1933_;
v_ngen_1909_ = v_ngen_1934_;
v_auxDeclNGen_1910_ = v_auxDeclNGen_1935_;
v_infoState_1911_ = v_infoState_1936_;
v_traceState_1912_ = v_traceState_1937_;
v_snapshotTasks_1913_ = v_snapshotTasks_1938_;
v_prevLinterStates_1914_ = v_prevLinterStates_1939_;
v_codeQualityEntryTasks_1915_ = v_codeQualityEntryTasks_1940_;
v___y_1916_ = v___x_1952_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_inc_ref_n(v_toEnvExtension_1942_, 2);
v___x_1953_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1942_, v_env_1928_);
lean_dec_ref(v_env_1928_);
v___x_1954_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1942_, v___x_1953_, v___f_1950_, v_asyncMode_1943_, v___x_1951_, v___x_1921_);
v___y_1902_ = v___x_1945_;
v___y_1903_ = v___y_1925_;
v_messages_1904_ = v_messages_1929_;
v_scopes_1905_ = v_scopes_1930_;
v_usedQuotCtxts_1906_ = v_usedQuotCtxts_1931_;
v_nextMacroScope_1907_ = v_nextMacroScope_1932_;
v_maxRecDepth_1908_ = v_maxRecDepth_1933_;
v_ngen_1909_ = v_ngen_1934_;
v_auxDeclNGen_1910_ = v_auxDeclNGen_1935_;
v_infoState_1911_ = v_infoState_1936_;
v_traceState_1912_ = v_traceState_1937_;
v_snapshotTasks_1913_ = v_snapshotTasks_1938_;
v_prevLinterStates_1914_ = v_prevLinterStates_1939_;
v_codeQualityEntryTasks_1915_ = v_codeQualityEntryTasks_1940_;
v___y_1916_ = v___x_1954_;
goto v___jp_1901_;
}
}
v___jp_1955_:
{
lean_object* v___x_1959_; lean_object* v_tag_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1959_ = lean_unsigned_to_nat(2u);
v_tag_1960_ = l_Lean_Syntax_getArg(v_x_1897_, v___x_1959_);
v___x_1961_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v_tag_1960_);
v___x_1962_ = l_Lean_Syntax_isOfKind(v_tag_1960_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_tag_1960_);
lean_dec(v_doc_1956_);
lean_dec(v_x_1897_);
v___x_1963_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1964_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1963_, v___y_1957_, v___y_1958_);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v_user_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1965_ = lean_unsigned_to_nat(3u);
v_user_1966_ = l_Lean_Syntax_getArg(v_x_1897_, v___x_1965_);
lean_dec(v_x_1897_);
v___x_1967_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_user_1966_);
v___x_1968_ = l_Lean_Syntax_isOfKind(v_user_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v_user_1966_);
lean_dec(v_tag_1960_);
lean_dec(v_doc_1956_);
v___x_1969_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1970_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1969_, v___y_1957_, v___y_1958_);
return v___x_1970_;
}
else
{
if (lean_obj_tag(v_doc_1956_) == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_box(0);
v___y_1923_ = v_user_1966_;
v___y_1924_ = v_tag_1960_;
v___y_1925_ = v___y_1958_;
v_a_1926_ = v___x_1971_;
goto v___jp_1922_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1989_; 
v_val_1972_ = lean_ctor_get(v_doc_1956_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_doc_1956_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1974_ = v_doc_1956_;
v_isShared_1975_ = v_isSharedCheck_1989_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v_doc_1956_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1989_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_val_1972_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v_a_1977_);
v___x_1979_ = v___x_1974_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v___y_1923_ = v_user_1966_;
v___y_1924_ = v_tag_1960_;
v___y_1925_ = v___y_1958_;
v_a_1926_ = v___x_1979_;
goto v___jp_1922_;
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_del_object(v___x_1974_);
lean_dec(v_user_1966_);
lean_dec(v_tag_1960_);
v_a_1981_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1976_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1976_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1897_ = stack[0].m_obj;
lean_object* v_a_1898_ = stack[1].m_obj;
lean_object* v_a_1899_ = stack[2].m_obj;
lean_object* v_res_2007_;
v_res_2007_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_1897_, v_a_1898_, v_a_1899_);
stack->m_obj
 = v_res_2007_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2012_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2021_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2022_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
v___x_2023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2024_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_2025_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2021_, v___x_2022_, v___x_2023_, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2026_;
v_res_2026_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
stack->m_obj
 = v_res_2026_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_2028_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_2057_ = l_Lean_addBuiltinDeclarationRanges(v___x_2055_, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2058_;
v_res_2058_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_2061_, lean_object* v_x_2062_){
_start:
{
if (lean_obj_tag(v_x_2062_) == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
return v___x_2063_;
}
else
{
lean_dec_ref(v___x_2061_);
lean_inc_ref(v_x_2062_);
return v_x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2064_, v_x_2065_);
lean_dec(v_x_2065_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_2067_, lean_object* v_k_2068_, lean_object* v_t_2069_){
_start:
{
if (lean_obj_tag(v_t_2069_) == 0)
{
lean_object* v_size_2070_; lean_object* v_k_2071_; lean_object* v_v_2072_; lean_object* v_l_2073_; lean_object* v_r_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2400_; 
v_size_2070_ = lean_ctor_get(v_t_2069_, 0);
v_k_2071_ = lean_ctor_get(v_t_2069_, 1);
v_v_2072_ = lean_ctor_get(v_t_2069_, 2);
v_l_2073_ = lean_ctor_get(v_t_2069_, 3);
v_r_2074_ = lean_ctor_get(v_t_2069_, 4);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_t_2069_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2076_ = v_t_2069_;
v_isShared_2077_ = v_isSharedCheck_2400_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_r_2074_);
lean_inc(v_l_2073_);
lean_inc(v_v_2072_);
lean_inc(v_k_2071_);
lean_inc(v_size_2070_);
lean_dec(v_t_2069_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2400_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
uint8_t v___x_2078_; 
v___x_2078_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2068_, v_k_2071_);
switch(v___x_2078_)
{
case 0:
{
lean_object* v_impl_2079_; lean_object* v___x_2080_; 
lean_del_object(v___x_2076_);
lean_dec(v_size_2070_);
v_impl_2079_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2067_, v_k_2068_, v_l_2073_);
v___x_2080_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2071_, v_v_2072_, v_impl_2079_, v_r_2074_);
return v___x_2080_;
}
case 1:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec(v_k_2071_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_v_2072_);
v___x_2082_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2067_, v___x_2081_);
lean_dec_ref_known(v___x_2081_, 1);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_del_object(v___x_2076_);
lean_dec(v_size_2070_);
lean_dec(v_k_2068_);
if (lean_obj_tag(v_l_2073_) == 0)
{
if (lean_obj_tag(v_r_2074_) == 0)
{
lean_object* v_size_2083_; lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v_l_2086_; lean_object* v_r_2087_; lean_object* v_size_2088_; lean_object* v_k_2089_; lean_object* v_v_2090_; lean_object* v_l_2091_; lean_object* v_r_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_size_2083_ = lean_ctor_get(v_l_2073_, 0);
v_k_2084_ = lean_ctor_get(v_l_2073_, 1);
v_v_2085_ = lean_ctor_get(v_l_2073_, 2);
v_l_2086_ = lean_ctor_get(v_l_2073_, 3);
v_r_2087_ = lean_ctor_get(v_l_2073_, 4);
lean_inc(v_r_2087_);
v_size_2088_ = lean_ctor_get(v_r_2074_, 0);
v_k_2089_ = lean_ctor_get(v_r_2074_, 1);
v_v_2090_ = lean_ctor_get(v_r_2074_, 2);
v_l_2091_ = lean_ctor_get(v_r_2074_, 3);
lean_inc(v_l_2091_);
v_r_2092_ = lean_ctor_get(v_r_2074_, 4);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_dec_lt(v_size_2083_, v_size_2088_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2230_; 
lean_inc(v_l_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_l_2073_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; 
v_unused_2231_ = lean_ctor_get(v_l_2073_, 4);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_l_2073_, 3);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_l_2073_, 2);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_l_2073_, 1);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_l_2073_, 0);
lean_dec(v_unused_2235_);
v___x_2096_ = v_l_2073_;
v_isShared_2097_ = v_isSharedCheck_2230_;
goto v_resetjp_2095_;
}
else
{
lean_dec(v_l_2073_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2230_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v_tree_2099_; 
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2084_, v_v_2085_, v_l_2086_, v_r_2087_);
v_tree_2099_ = lean_ctor_get(v___x_2098_, 2);
if (lean_obj_tag(v_tree_2099_) == 0)
{
lean_object* v_k_2100_; lean_object* v_v_2101_; lean_object* v_size_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_inc_ref(v_tree_2099_);
v_k_2100_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_k_2100_);
v_v_2101_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_v_2101_);
lean_dec_ref(v___x_2098_);
v_size_2102_ = lean_ctor_get(v_tree_2099_, 0);
v___x_2103_ = lean_unsigned_to_nat(3u);
v___x_2104_ = lean_nat_mul(v___x_2103_, v_size_2102_);
v___x_2105_ = lean_nat_dec_lt(v___x_2104_, v_size_2088_);
lean_dec(v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_l_2091_);
v___x_2106_ = lean_nat_add(v___x_2093_, v_size_2102_);
v___x_2107_ = lean_nat_add(v___x_2106_, v_size_2088_);
lean_dec(v___x_2106_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v_r_2074_);
lean_ctor_set(v___x_2096_, 3, v_tree_2099_);
lean_ctor_set(v___x_2096_, 2, v_v_2101_);
lean_ctor_set(v___x_2096_, 1, v_k_2100_);
lean_ctor_set(v___x_2096_, 0, v___x_2107_);
v___x_2109_ = v___x_2096_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_k_2100_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_v_2101_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_tree_2099_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_r_2074_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2165_; 
lean_inc(v_r_2092_);
lean_inc(v_v_2090_);
lean_inc(v_k_2089_);
lean_inc(v_size_2088_);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2166_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_r_2074_, 2);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_r_2074_, 1);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_r_2074_, 0);
lean_dec(v_unused_2170_);
v___x_2112_ = v_r_2074_;
v_isShared_2113_ = v_isSharedCheck_2165_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v_r_2074_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2165_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_size_2114_; lean_object* v_k_2115_; lean_object* v_v_2116_; lean_object* v_l_2117_; lean_object* v_r_2118_; lean_object* v_size_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_size_2114_ = lean_ctor_get(v_l_2091_, 0);
v_k_2115_ = lean_ctor_get(v_l_2091_, 1);
v_v_2116_ = lean_ctor_get(v_l_2091_, 2);
v_l_2117_ = lean_ctor_get(v_l_2091_, 3);
v_r_2118_ = lean_ctor_get(v_l_2091_, 4);
v_size_2119_ = lean_ctor_get(v_r_2092_, 0);
v___x_2120_ = lean_unsigned_to_nat(2u);
v___x_2121_ = lean_nat_mul(v___x_2120_, v_size_2119_);
v___x_2122_ = lean_nat_dec_lt(v_size_2114_, v___x_2121_);
lean_dec(v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2150_; 
lean_inc(v_r_2118_);
lean_inc(v_l_2117_);
lean_inc(v_v_2116_);
lean_inc(v_k_2115_);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_l_2091_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; lean_object* v_unused_2152_; lean_object* v_unused_2153_; lean_object* v_unused_2154_; lean_object* v_unused_2155_; 
v_unused_2151_ = lean_ctor_get(v_l_2091_, 4);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_l_2091_, 3);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_l_2091_, 2);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v_l_2091_, 1);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_l_2091_, 0);
lean_dec(v_unused_2155_);
v___x_2124_ = v_l_2091_;
v_isShared_2125_ = v_isSharedCheck_2150_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v_l_2091_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2150_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2140_; 
v___x_2126_ = lean_nat_add(v___x_2093_, v_size_2102_);
v___x_2127_ = lean_nat_add(v___x_2126_, v_size_2088_);
lean_dec(v_size_2088_);
if (lean_obj_tag(v_l_2117_) == 0)
{
lean_object* v_size_2148_; 
v_size_2148_ = lean_ctor_get(v_l_2117_, 0);
lean_inc(v_size_2148_);
v___y_2140_ = v_size_2148_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v___y_2140_ = v___x_2149_;
goto v___jp_2139_;
}
v___jp_2128_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = lean_nat_add(v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 4, v_r_2092_);
lean_ctor_set(v___x_2124_, 3, v_r_2118_);
lean_ctor_set(v___x_2124_, 2, v_v_2090_);
lean_ctor_set(v___x_2124_, 1, v_k_2089_);
lean_ctor_set(v___x_2124_, 0, v___x_2132_);
v___x_2134_ = v___x_2124_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_r_2118_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_r_2092_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 4, v___x_2134_);
lean_ctor_set(v___x_2112_, 3, v___y_2129_);
lean_ctor_set(v___x_2112_, 2, v_v_2116_);
lean_ctor_set(v___x_2112_, 1, v_k_2115_);
lean_ctor_set(v___x_2112_, 0, v___x_2127_);
v___x_2136_ = v___x_2112_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v___y_2129_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
v___jp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_nat_add(v___x_2126_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec(v___x_2126_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v_l_2117_);
lean_ctor_set(v___x_2096_, 3, v_tree_2099_);
lean_ctor_set(v___x_2096_, 2, v_v_2101_);
lean_ctor_set(v___x_2096_, 1, v_k_2100_);
lean_ctor_set(v___x_2096_, 0, v___x_2141_);
v___x_2143_ = v___x_2096_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_2100_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_2101_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_tree_2099_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_l_2117_);
v___x_2143_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_nat_add(v___x_2093_, v_size_2119_);
if (lean_obj_tag(v_r_2118_) == 0)
{
lean_object* v_size_2145_; 
v_size_2145_ = lean_ctor_get(v_r_2118_, 0);
lean_inc(v_size_2145_);
v___y_2129_ = v___x_2143_;
v___y_2130_ = v___x_2144_;
v___y_2131_ = v_size_2145_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___y_2129_ = v___x_2143_;
v___y_2130_ = v___x_2144_;
v___y_2131_ = v___x_2146_;
goto v___jp_2128_;
}
}
}
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2156_ = lean_nat_add(v___x_2093_, v_size_2102_);
v___x_2157_ = lean_nat_add(v___x_2156_, v_size_2088_);
lean_dec(v_size_2088_);
v___x_2158_ = lean_nat_add(v___x_2156_, v_size_2114_);
lean_dec(v___x_2156_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 4, v_l_2091_);
lean_ctor_set(v___x_2112_, 3, v_tree_2099_);
lean_ctor_set(v___x_2112_, 2, v_v_2101_);
lean_ctor_set(v___x_2112_, 1, v_k_2100_);
lean_ctor_set(v___x_2112_, 0, v___x_2158_);
v___x_2160_ = v___x_2112_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2100_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2101_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_tree_2099_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_l_2091_);
v___x_2160_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2162_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v_r_2092_);
lean_ctor_set(v___x_2096_, 3, v___x_2160_);
lean_ctor_set(v___x_2096_, 2, v_v_2090_);
lean_ctor_set(v___x_2096_, 1, v_k_2089_);
lean_ctor_set(v___x_2096_, 0, v___x_2157_);
v___x_2162_ = v___x_2096_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_r_2092_);
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
lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2224_; 
lean_inc(v_r_2092_);
lean_inc(v_v_2090_);
lean_inc(v_k_2089_);
lean_inc(v_size_2088_);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2225_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_r_2074_, 2);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_r_2074_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_r_2074_, 0);
lean_dec(v_unused_2229_);
v___x_2172_ = v_r_2074_;
v_isShared_2173_ = v_isSharedCheck_2224_;
goto v_resetjp_2171_;
}
else
{
lean_dec(v_r_2074_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2224_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
if (lean_obj_tag(v_l_2091_) == 0)
{
if (lean_obj_tag(v_r_2092_) == 0)
{
lean_object* v_k_2174_; lean_object* v_v_2175_; lean_object* v_size_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_inc(v_tree_2099_);
v_k_2174_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_k_2174_);
v_v_2175_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_v_2175_);
lean_dec_ref(v___x_2098_);
v_size_2176_ = lean_ctor_get(v_l_2091_, 0);
v___x_2177_ = lean_nat_add(v___x_2093_, v_size_2088_);
lean_dec(v_size_2088_);
v___x_2178_ = lean_nat_add(v___x_2093_, v_size_2176_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 4, v_l_2091_);
lean_ctor_set(v___x_2172_, 3, v_tree_2099_);
lean_ctor_set(v___x_2172_, 2, v_v_2175_);
lean_ctor_set(v___x_2172_, 1, v_k_2174_);
lean_ctor_set(v___x_2172_, 0, v___x_2178_);
v___x_2180_ = v___x_2172_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_tree_2099_);
lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_l_2091_);
v___x_2180_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v_r_2092_);
lean_ctor_set(v___x_2096_, 3, v___x_2180_);
lean_ctor_set(v___x_2096_, 2, v_v_2090_);
lean_ctor_set(v___x_2096_, 1, v_k_2089_);
lean_ctor_set(v___x_2096_, 0, v___x_2177_);
v___x_2182_ = v___x_2096_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_r_2092_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_k_2185_; lean_object* v_v_2186_; lean_object* v_k_2187_; lean_object* v_v_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_size_2088_);
v_k_2185_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_k_2185_);
v_v_2186_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_v_2186_);
lean_dec_ref(v___x_2098_);
v_k_2187_ = lean_ctor_get(v_l_2091_, 1);
v_v_2188_ = lean_ctor_get(v_l_2091_, 2);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_l_2091_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; lean_object* v_unused_2204_; lean_object* v_unused_2205_; 
v_unused_2203_ = lean_ctor_get(v_l_2091_, 4);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_l_2091_, 3);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_l_2091_, 0);
lean_dec(v_unused_2205_);
v___x_2190_ = v_l_2091_;
v_isShared_2191_ = v_isSharedCheck_2202_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_v_2188_);
lean_inc(v_k_2187_);
lean_dec(v_l_2091_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2202_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_unsigned_to_nat(3u);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 4, v_r_2092_);
lean_ctor_set(v___x_2190_, 3, v_r_2092_);
lean_ctor_set(v___x_2190_, 2, v_v_2186_);
lean_ctor_set(v___x_2190_, 1, v_k_2185_);
lean_ctor_set(v___x_2190_, 0, v___x_2093_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2185_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2186_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_2092_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_r_2092_);
v___x_2194_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 3, v_r_2092_);
lean_ctor_set(v___x_2172_, 0, v___x_2093_);
v___x_2196_ = v___x_2172_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_r_2092_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_r_2092_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v___x_2196_);
lean_ctor_set(v___x_2096_, 3, v___x_2194_);
lean_ctor_set(v___x_2096_, 2, v_v_2188_);
lean_ctor_set(v___x_2096_, 1, v_k_2187_);
lean_ctor_set(v___x_2096_, 0, v___x_2192_);
v___x_2198_ = v___x_2096_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2187_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2188_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2092_) == 0)
{
lean_object* v_k_2206_; lean_object* v_v_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v_size_2088_);
v_k_2206_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_k_2206_);
v_v_2207_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_v_2207_);
lean_dec_ref(v___x_2098_);
v___x_2208_ = lean_unsigned_to_nat(3u);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 4, v_l_2091_);
lean_ctor_set(v___x_2172_, 2, v_v_2207_);
lean_ctor_set(v___x_2172_, 1, v_k_2206_);
lean_ctor_set(v___x_2172_, 0, v___x_2093_);
v___x_2210_ = v___x_2172_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_l_2091_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_l_2091_);
v___x_2210_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v_r_2092_);
lean_ctor_set(v___x_2096_, 3, v___x_2210_);
lean_ctor_set(v___x_2096_, 2, v_v_2090_);
lean_ctor_set(v___x_2096_, 1, v_k_2089_);
lean_ctor_set(v___x_2096_, 0, v___x_2208_);
v___x_2212_ = v___x_2096_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v_r_2092_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_k_2215_; lean_object* v_v_2216_; lean_object* v___x_2218_; 
v_k_2215_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_k_2215_);
v_v_2216_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_v_2216_);
lean_dec_ref(v___x_2098_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 3, v_r_2092_);
v___x_2218_ = v___x_2172_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_size_2088_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_r_2092_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_r_2092_);
v___x_2218_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_unsigned_to_nat(2u);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 4, v___x_2218_);
lean_ctor_set(v___x_2096_, 3, v_r_2092_);
lean_ctor_set(v___x_2096_, 2, v_v_2216_);
lean_ctor_set(v___x_2096_, 1, v_k_2215_);
lean_ctor_set(v___x_2096_, 0, v___x_2219_);
v___x_2221_ = v___x_2096_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_k_2215_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_v_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_r_2092_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v___x_2218_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
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
lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2388_; 
lean_inc(v_r_2092_);
lean_inc(v_v_2090_);
lean_inc(v_k_2089_);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_r_2074_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; lean_object* v_unused_2390_; lean_object* v_unused_2391_; lean_object* v_unused_2392_; lean_object* v_unused_2393_; 
v_unused_2389_ = lean_ctor_get(v_r_2074_, 4);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_r_2074_, 3);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_r_2074_, 2);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_r_2074_, 1);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_r_2074_, 0);
lean_dec(v_unused_2393_);
v___x_2237_ = v_r_2074_;
v_isShared_2238_ = v_isSharedCheck_2388_;
goto v_resetjp_2236_;
}
else
{
lean_dec(v_r_2074_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2388_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v_tree_2240_; 
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2089_, v_v_2090_, v_l_2091_, v_r_2092_);
v_tree_2240_ = lean_ctor_get(v___x_2239_, 2);
lean_inc(v_tree_2240_);
if (lean_obj_tag(v_tree_2240_) == 0)
{
lean_object* v_k_2241_; lean_object* v_v_2242_; lean_object* v_size_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_k_2241_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_k_2241_);
v_v_2242_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_v_2242_);
lean_dec_ref(v___x_2239_);
v_size_2243_ = lean_ctor_get(v_tree_2240_, 0);
v___x_2244_ = lean_unsigned_to_nat(3u);
v___x_2245_ = lean_nat_mul(v___x_2244_, v_size_2243_);
v___x_2246_ = lean_nat_dec_lt(v___x_2245_, v_size_2083_);
lean_dec(v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_dec(v_r_2087_);
v___x_2247_ = lean_nat_add(v___x_2093_, v_size_2083_);
v___x_2248_ = lean_nat_add(v___x_2247_, v_size_2243_);
lean_dec(v___x_2247_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_tree_2240_);
lean_ctor_set(v___x_2237_, 3, v_l_2073_);
lean_ctor_set(v___x_2237_, 2, v_v_2242_);
lean_ctor_set(v___x_2237_, 1, v_k_2241_);
lean_ctor_set(v___x_2237_, 0, v___x_2248_);
v___x_2250_ = v___x_2237_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2241_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2242_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_l_2073_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_tree_2240_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2317_; 
lean_inc(v_l_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_inc(v_size_2083_);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_l_2073_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; lean_object* v_unused_2319_; lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; 
v_unused_2318_ = lean_ctor_get(v_l_2073_, 4);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_l_2073_, 3);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_l_2073_, 2);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_l_2073_, 1);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_l_2073_, 0);
lean_dec(v_unused_2322_);
v___x_2253_ = v_l_2073_;
v_isShared_2254_ = v_isSharedCheck_2317_;
goto v_resetjp_2252_;
}
else
{
lean_dec(v_l_2073_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2317_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_size_2255_; lean_object* v_size_2256_; lean_object* v_k_2257_; lean_object* v_v_2258_; lean_object* v_l_2259_; lean_object* v_r_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_size_2255_ = lean_ctor_get(v_l_2086_, 0);
v_size_2256_ = lean_ctor_get(v_r_2087_, 0);
v_k_2257_ = lean_ctor_get(v_r_2087_, 1);
v_v_2258_ = lean_ctor_get(v_r_2087_, 2);
v_l_2259_ = lean_ctor_get(v_r_2087_, 3);
v_r_2260_ = lean_ctor_get(v_r_2087_, 4);
v___x_2261_ = lean_unsigned_to_nat(2u);
v___x_2262_ = lean_nat_mul(v___x_2261_, v_size_2255_);
v___x_2263_ = lean_nat_dec_lt(v_size_2256_, v___x_2262_);
lean_dec(v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2301_; 
lean_inc(v_r_2260_);
lean_inc(v_l_2259_);
lean_inc(v_v_2258_);
lean_inc(v_k_2257_);
lean_del_object(v___x_2253_);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_r_2087_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; lean_object* v_unused_2303_; lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; 
v_unused_2302_ = lean_ctor_get(v_r_2087_, 4);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_r_2087_, 3);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_r_2087_, 2);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_r_2087_, 1);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_r_2087_, 0);
lean_dec(v_unused_2306_);
v___x_2265_ = v_r_2087_;
v_isShared_2266_ = v_isSharedCheck_2301_;
goto v_resetjp_2264_;
}
else
{
lean_dec(v_r_2087_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2301_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___x_2289_; lean_object* v___y_2291_; 
v___x_2267_ = lean_nat_add(v___x_2093_, v_size_2083_);
lean_dec(v_size_2083_);
v___x_2268_ = lean_nat_add(v___x_2267_, v_size_2243_);
lean_dec(v___x_2267_);
v___x_2289_ = lean_nat_add(v___x_2093_, v_size_2255_);
if (lean_obj_tag(v_l_2259_) == 0)
{
lean_object* v_size_2299_; 
v_size_2299_ = lean_ctor_get(v_l_2259_, 0);
lean_inc(v_size_2299_);
v___y_2291_ = v_size_2299_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___y_2291_ = v___x_2300_;
goto v___jp_2290_;
}
v___jp_2269_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_nat_add(v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec(v___y_2271_);
lean_inc_ref(v_tree_2240_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 4, v_tree_2240_);
lean_ctor_set(v___x_2265_, 3, v_r_2260_);
lean_ctor_set(v___x_2265_, 2, v_v_2242_);
lean_ctor_set(v___x_2265_, 1, v_k_2241_);
lean_ctor_set(v___x_2265_, 0, v___x_2273_);
v___x_2275_ = v___x_2265_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_k_2241_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_v_2242_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_r_2260_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_tree_2240_);
v___x_2275_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_isSharedCheck_2282_ = !lean_is_exclusive(v_tree_2240_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; lean_object* v_unused_2284_; lean_object* v_unused_2285_; lean_object* v_unused_2286_; lean_object* v_unused_2287_; 
v_unused_2283_ = lean_ctor_get(v_tree_2240_, 4);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v_tree_2240_, 3);
lean_dec(v_unused_2284_);
v_unused_2285_ = lean_ctor_get(v_tree_2240_, 2);
lean_dec(v_unused_2285_);
v_unused_2286_ = lean_ctor_get(v_tree_2240_, 1);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_tree_2240_, 0);
lean_dec(v_unused_2287_);
v___x_2277_ = v_tree_2240_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_tree_2240_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 4, v___x_2275_);
lean_ctor_set(v___x_2277_, 3, v___y_2270_);
lean_ctor_set(v___x_2277_, 2, v_v_2258_);
lean_ctor_set(v___x_2277_, 1, v_k_2257_);
lean_ctor_set(v___x_2277_, 0, v___x_2268_);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_k_2257_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_v_2258_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v___y_2270_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v___x_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
v___jp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2292_ = lean_nat_add(v___x_2289_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec(v___x_2289_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_l_2259_);
lean_ctor_set(v___x_2237_, 3, v_l_2086_);
lean_ctor_set(v___x_2237_, 2, v_v_2085_);
lean_ctor_set(v___x_2237_, 1, v_k_2084_);
lean_ctor_set(v___x_2237_, 0, v___x_2292_);
v___x_2294_ = v___x_2237_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2298_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2298_, 4, v_l_2259_);
v___x_2294_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_nat_add(v___x_2093_, v_size_2243_);
if (lean_obj_tag(v_r_2260_) == 0)
{
lean_object* v_size_2296_; 
v_size_2296_ = lean_ctor_get(v_r_2260_, 0);
lean_inc(v_size_2296_);
v___y_2270_ = v___x_2294_;
v___y_2271_ = v___x_2295_;
v___y_2272_ = v_size_2296_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_unsigned_to_nat(0u);
v___y_2270_ = v___x_2294_;
v___y_2271_ = v___x_2295_;
v___y_2272_ = v___x_2297_;
goto v___jp_2269_;
}
}
}
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2307_ = lean_nat_add(v___x_2093_, v_size_2083_);
lean_dec(v_size_2083_);
v___x_2308_ = lean_nat_add(v___x_2307_, v_size_2243_);
lean_dec(v___x_2307_);
v___x_2309_ = lean_nat_add(v___x_2093_, v_size_2243_);
v___x_2310_ = lean_nat_add(v___x_2309_, v_size_2256_);
lean_dec(v___x_2309_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_tree_2240_);
lean_ctor_set(v___x_2237_, 3, v_r_2087_);
lean_ctor_set(v___x_2237_, 2, v_v_2242_);
lean_ctor_set(v___x_2237_, 1, v_k_2241_);
lean_ctor_set(v___x_2237_, 0, v___x_2310_);
v___x_2312_ = v___x_2237_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_k_2241_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_v_2242_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_r_2087_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v_tree_2240_);
v___x_2312_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 4, v___x_2312_);
lean_ctor_set(v___x_2253_, 0, v___x_2308_);
v___x_2314_ = v___x_2253_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2086_) == 0)
{
lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2346_; 
lean_inc_ref(v_l_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_inc(v_size_2083_);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_l_2073_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; lean_object* v_unused_2348_; lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; 
v_unused_2347_ = lean_ctor_get(v_l_2073_, 4);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_l_2073_, 3);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_l_2073_, 2);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_l_2073_, 1);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_l_2073_, 0);
lean_dec(v_unused_2351_);
v___x_2324_ = v_l_2073_;
v_isShared_2325_ = v_isSharedCheck_2346_;
goto v_resetjp_2323_;
}
else
{
lean_dec(v_l_2073_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2346_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
if (lean_obj_tag(v_r_2087_) == 0)
{
lean_object* v_k_2326_; lean_object* v_v_2327_; lean_object* v_size_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v_k_2326_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_k_2326_);
v_v_2327_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_v_2327_);
lean_dec_ref(v___x_2239_);
v_size_2328_ = lean_ctor_get(v_r_2087_, 0);
v___x_2329_ = lean_nat_add(v___x_2093_, v_size_2083_);
lean_dec(v_size_2083_);
v___x_2330_ = lean_nat_add(v___x_2093_, v_size_2328_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_tree_2240_);
lean_ctor_set(v___x_2237_, 3, v_r_2087_);
lean_ctor_set(v___x_2237_, 2, v_v_2327_);
lean_ctor_set(v___x_2237_, 1, v_k_2326_);
lean_ctor_set(v___x_2237_, 0, v___x_2330_);
v___x_2332_ = v___x_2237_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2326_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2327_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_r_2087_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_tree_2240_);
v___x_2332_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 4, v___x_2332_);
lean_ctor_set(v___x_2324_, 0, v___x_2329_);
v___x_2334_ = v___x_2324_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
else
{
lean_object* v_k_2337_; lean_object* v_v_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_dec(v_size_2083_);
v_k_2337_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_k_2337_);
v_v_2338_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_v_2338_);
lean_dec_ref(v___x_2239_);
v___x_2339_ = lean_unsigned_to_nat(3u);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_r_2087_);
lean_ctor_set(v___x_2237_, 3, v_r_2087_);
lean_ctor_set(v___x_2237_, 2, v_v_2338_);
lean_ctor_set(v___x_2237_, 1, v_k_2337_);
lean_ctor_set(v___x_2237_, 0, v___x_2093_);
v___x_2341_ = v___x_2237_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_k_2337_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_v_2338_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_r_2087_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_r_2087_);
v___x_2341_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 4, v___x_2341_);
lean_ctor_set(v___x_2324_, 0, v___x_2339_);
v___x_2343_ = v___x_2324_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v___x_2341_);
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
else
{
if (lean_obj_tag(v_r_2087_) == 0)
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2376_; 
lean_inc(v_l_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_l_2073_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; 
v_unused_2377_ = lean_ctor_get(v_l_2073_, 4);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_l_2073_, 3);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_l_2073_, 2);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_l_2073_, 1);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_l_2073_, 0);
lean_dec(v_unused_2381_);
v___x_2353_ = v_l_2073_;
v_isShared_2354_ = v_isSharedCheck_2376_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v_l_2073_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2376_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_k_2355_; lean_object* v_v_2356_; lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2372_; 
v_k_2355_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_k_2355_);
v_v_2356_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_v_2356_);
lean_dec_ref(v___x_2239_);
v_k_2357_ = lean_ctor_get(v_r_2087_, 1);
v_v_2358_ = lean_ctor_get(v_r_2087_, 2);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_r_2087_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; lean_object* v_unused_2374_; lean_object* v_unused_2375_; 
v_unused_2373_ = lean_ctor_get(v_r_2087_, 4);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_r_2087_, 3);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_r_2087_, 0);
lean_dec(v_unused_2375_);
v___x_2360_ = v_r_2087_;
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_v_2358_);
lean_inc(v_k_2357_);
lean_dec(v_r_2087_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(3u);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 4, v_l_2086_);
lean_ctor_set(v___x_2360_, 3, v_l_2086_);
lean_ctor_set(v___x_2360_, 2, v_v_2085_);
lean_ctor_set(v___x_2360_, 1, v_k_2084_);
lean_ctor_set(v___x_2360_, 0, v___x_2093_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_l_2086_);
v___x_2364_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_l_2086_);
lean_ctor_set(v___x_2237_, 3, v_l_2086_);
lean_ctor_set(v___x_2237_, 2, v_v_2356_);
lean_ctor_set(v___x_2237_, 1, v_k_2355_);
lean_ctor_set(v___x_2237_, 0, v___x_2093_);
v___x_2366_ = v___x_2237_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_k_2355_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_v_2356_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_l_2086_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 4, v___x_2366_);
lean_ctor_set(v___x_2353_, 3, v___x_2364_);
lean_ctor_set(v___x_2353_, 2, v_v_2358_);
lean_ctor_set(v___x_2353_, 1, v_k_2357_);
lean_ctor_set(v___x_2353_, 0, v___x_2362_);
v___x_2368_ = v___x_2353_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_k_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_v_2358_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
else
{
lean_object* v_k_2382_; lean_object* v_v_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v_k_2382_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_k_2382_);
v_v_2383_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_v_2383_);
lean_dec_ref(v___x_2239_);
v___x_2384_ = lean_unsigned_to_nat(2u);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_r_2087_);
lean_ctor_set(v___x_2237_, 3, v_l_2073_);
lean_ctor_set(v___x_2237_, 2, v_v_2383_);
lean_ctor_set(v___x_2237_, 1, v_k_2382_);
lean_ctor_set(v___x_2237_, 0, v___x_2384_);
v___x_2386_ = v___x_2237_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_k_2382_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_v_2383_);
lean_ctor_set(v_reuseFailAlloc_2387_, 3, v_l_2073_);
lean_ctor_set(v_reuseFailAlloc_2387_, 4, v_r_2087_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
}
else
{
return v_l_2073_;
}
}
else
{
return v_r_2074_;
}
}
else
{
lean_object* v_val_2394_; lean_object* v___x_2396_; 
v_val_2394_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2394_);
lean_dec_ref_known(v___x_2082_, 1);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 2, v_val_2394_);
lean_ctor_set(v___x_2076_, 1, v_k_2068_);
v___x_2396_ = v___x_2076_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_size_2070_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2068_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_val_2394_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_l_2073_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_r_2074_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
default: 
{
lean_object* v_impl_2398_; lean_object* v___x_2399_; 
lean_del_object(v___x_2076_);
lean_dec(v_size_2070_);
v_impl_2398_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2067_, v_k_2068_, v_r_2074_);
v___x_2399_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2071_, v_v_2072_, v_l_2073_, v_impl_2398_);
return v___x_2399_;
}
}
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2067_, v___x_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_dec(v_k_2068_);
return v_t_2069_;
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_val_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v_k_2068_);
lean_ctor_set(v___x_2405_, 2, v_val_2403_);
lean_ctor_set(v___x_2405_, 3, v_t_2069_);
lean_ctor_set(v___x_2405_, 4, v_t_2069_);
return v___x_2405_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2406_, lean_object* v_i_2407_, lean_object* v_k_2408_){
_start:
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = lean_array_get_size(v_keys_2406_);
v___x_2410_ = lean_nat_dec_lt(v_i_2407_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_dec(v_i_2407_);
return v___x_2410_;
}
else
{
lean_object* v_k_x27_2411_; uint8_t v___x_2412_; 
v_k_x27_2411_ = lean_array_fget_borrowed(v_keys_2406_, v_i_2407_);
v___x_2412_ = lean_name_eq(v_k_2408_, v_k_x27_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_add(v_i_2407_, v___x_2413_);
lean_dec(v_i_2407_);
v_i_2407_ = v___x_2414_;
goto _start;
}
else
{
lean_dec(v_i_2407_);
return v___x_2410_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2406_ = stack[0].m_obj;
lean_object* v_i_2407_ = stack[1].m_obj;
lean_object* v_k_2408_ = stack[2].m_obj;
uint8_t v_res_2416_;
v_res_2416_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2406_, v_i_2407_, v_k_2408_);
stack->m_num = v_res_2416_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2417_, lean_object* v_i_2418_, lean_object* v_k_2419_){
_start:
{
uint8_t v_res_2420_; lean_object* v_r_2421_; 
v_res_2420_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2417_, v_i_2418_, v_k_2419_);
lean_dec(v_k_2419_);
lean_dec_ref(v_keys_2417_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_2422_, size_t v_x_2423_, lean_object* v_x_2424_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
lean_object* v_es_2425_; lean_object* v___x_2426_; size_t v___x_2427_; size_t v___x_2428_; lean_object* v_j_2429_; lean_object* v___x_2430_; 
v_es_2425_ = lean_ctor_get(v_x_2422_, 0);
v___x_2426_ = lean_box(2);
v___x_2427_ = ((size_t)31ULL);
v___x_2428_ = lean_usize_land(v_x_2423_, v___x_2427_);
v_j_2429_ = lean_usize_to_nat(v___x_2428_);
v___x_2430_ = lean_array_get_borrowed(v___x_2426_, v_es_2425_, v_j_2429_);
lean_dec(v_j_2429_);
switch(lean_obj_tag(v___x_2430_))
{
case 0:
{
lean_object* v_key_2431_; uint8_t v___x_2432_; 
v_key_2431_ = lean_ctor_get(v___x_2430_, 0);
v___x_2432_ = lean_name_eq(v_x_2424_, v_key_2431_);
return v___x_2432_;
}
case 1:
{
lean_object* v_node_2433_; size_t v___x_2434_; size_t v___x_2435_; 
v_node_2433_ = lean_ctor_get(v___x_2430_, 0);
v___x_2434_ = ((size_t)5ULL);
v___x_2435_ = lean_usize_shift_right(v_x_2423_, v___x_2434_);
v_x_2422_ = v_node_2433_;
v_x_2423_ = v___x_2435_;
goto _start;
}
default: 
{
uint8_t v___x_2437_; 
v___x_2437_ = 0;
return v___x_2437_;
}
}
}
else
{
lean_object* v_ks_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_ks_2438_ = lean_ctor_get(v_x_2422_, 0);
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_2438_, v___x_2439_, v_x_2424_);
return v___x_2440_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2422_ = stack[0].m_obj;
size_t v_x_2423_ = stack[1].m_num;
lean_object* v_x_2424_ = stack[2].m_obj;
uint8_t v_res_2441_;
v_res_2441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2422_, v_x_2423_, v_x_2424_);
stack->m_num = v_res_2441_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
size_t v_x_4175__boxed_2445_; uint8_t v_res_2446_; lean_object* v_r_2447_; 
v_x_4175__boxed_2445_ = lean_unbox_usize(v_x_2443_);
lean_dec(v_x_2443_);
v_res_2446_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2442_, v_x_4175__boxed_2445_, v_x_2444_);
lean_dec(v_x_2444_);
lean_dec_ref(v_x_2442_);
v_r_2447_ = lean_box(v_res_2446_);
return v_r_2447_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
uint64_t v___y_2451_; 
if (lean_obj_tag(v_x_2449_) == 0)
{
uint64_t v___x_2454_; 
v___x_2454_ = 1723ULL;
v___y_2451_ = v___x_2454_;
goto v___jp_2450_;
}
else
{
uint64_t v_hash_2455_; 
v_hash_2455_ = lean_ctor_get_uint64(v_x_2449_, sizeof(void*)*2);
v___y_2451_ = v_hash_2455_;
goto v___jp_2450_;
}
v___jp_2450_:
{
size_t v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = lean_uint64_to_usize(v___y_2451_);
v___x_2453_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2448_, v___x_2452_, v_x_2449_);
return v___x_2453_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2448_ = stack[0].m_obj;
lean_object* v_x_2449_ = stack[1].m_obj;
uint8_t v_res_2456_;
v_res_2456_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2448_, v_x_2449_);
stack->m_num = v_res_2456_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2457_, v_x_2458_);
lean_dec(v_x_2458_);
lean_dec_ref(v_x_2457_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_2461_, lean_object* v_a_2462_, uint8_t v___x_2463_, lean_object* v_x_2464_, lean_object* v_____s_2465_){
_start:
{
lean_object* v_fst_2466_; lean_object* v_kinds_2467_; uint8_t v___x_2468_; 
v_fst_2466_ = lean_ctor_get(v_x_2464_, 0);
lean_inc(v_fst_2466_);
lean_dec_ref(v_x_2464_);
v_kinds_2467_ = lean_ctor_get(v_tactics_2461_, 1);
v___x_2468_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_2467_, v_fst_2466_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
lean_dec(v_fst_2466_);
lean_dec(v_a_2462_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_____s_2465_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = l_Lean_Name_toString(v_a_2462_, v___x_2463_);
v___x_2471_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2470_, v_fst_2466_, v_____s_2465_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tactics_2461_ = stack[0].m_obj;
lean_object* v_a_2462_ = stack[1].m_obj;
uint8_t v___x_2463_ = stack[2].m_num;
lean_object* v_x_2464_ = stack[3].m_obj;
lean_object* v_____s_2465_ = stack[4].m_obj;
lean_object* v_res_2473_;
v_res_2473_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2461_, v_a_2462_, v___x_2463_, v_x_2464_, v_____s_2465_);
stack->m_obj
 = v_res_2473_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_2474_, lean_object* v_a_2475_, lean_object* v___x_2476_, lean_object* v_x_2477_, lean_object* v_____s_2478_){
_start:
{
uint8_t v___x_4261__boxed_2479_; lean_object* v_res_2480_; 
v___x_4261__boxed_2479_ = lean_unbox(v___x_2476_);
v_res_2480_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2474_, v_a_2475_, v___x_4261__boxed_2479_, v_x_2477_, v_____s_2478_);
lean_dec_ref(v_tactics_2474_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_2481_, lean_object* v_keys_2482_, lean_object* v_vals_2483_, lean_object* v_i_2484_, lean_object* v_acc_2485_){
_start:
{
lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2486_ = lean_array_get_size(v_keys_2482_);
v___x_2487_ = lean_nat_dec_lt(v_i_2484_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
lean_dec(v_i_2484_);
lean_dec_ref(v_f_2481_);
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_acc_2485_);
return v___x_2488_;
}
else
{
lean_object* v_k_2489_; lean_object* v_v_2490_; lean_object* v___x_2491_; 
v_k_2489_ = lean_array_fget_borrowed(v_keys_2482_, v_i_2484_);
v_v_2490_ = lean_array_fget_borrowed(v_vals_2483_, v_i_2484_);
lean_inc_ref(v_f_2481_);
lean_inc(v_v_2490_);
lean_inc(v_k_2489_);
v___x_2491_ = lean_apply_3(v_f_2481_, v_acc_2485_, v_k_2489_, v_v_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_dec(v_i_2484_);
lean_dec_ref(v_f_2481_);
return v___x_2491_;
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = lean_unsigned_to_nat(1u);
v___x_2494_ = lean_nat_add(v_i_2484_, v___x_2493_);
lean_dec(v_i_2484_);
v_i_2484_ = v___x_2494_;
v_acc_2485_ = v_a_2492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_2496_, lean_object* v_keys_2497_, lean_object* v_vals_2498_, lean_object* v_i_2499_, lean_object* v_acc_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2496_, v_keys_2497_, v_vals_2498_, v_i_2499_, v_acc_2500_);
lean_dec_ref(v_vals_2498_);
lean_dec_ref(v_keys_2497_);
return v_res_2501_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_2502_, lean_object* v_as_2503_, size_t v_i_2504_, size_t v_stop_2505_, lean_object* v_b_2506_){
_start:
{
lean_object* v_a_2508_; lean_object* v___y_2513_; uint8_t v___x_2515_; 
v___x_2515_ = lean_usize_dec_eq(v_i_2504_, v_stop_2505_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_array_uget_borrowed(v_as_2503_, v_i_2504_);
switch(lean_obj_tag(v___x_2516_))
{
case 0:
{
lean_object* v_key_2517_; lean_object* v_val_2518_; lean_object* v___x_2519_; 
v_key_2517_ = lean_ctor_get(v___x_2516_, 0);
v_val_2518_ = lean_ctor_get(v___x_2516_, 1);
lean_inc_ref(v_f_2502_);
lean_inc(v_val_2518_);
lean_inc(v_key_2517_);
v___x_2519_ = lean_apply_3(v_f_2502_, v_b_2506_, v_key_2517_, v_val_2518_);
v___y_2513_ = v___x_2519_;
goto v___jp_2512_;
}
case 1:
{
lean_object* v_node_2520_; lean_object* v___x_2521_; 
v_node_2520_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_node_2520_);
lean_inc_ref(v_f_2502_);
v___x_2521_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2502_, v_node_2520_, v_b_2506_);
v___y_2513_ = v___x_2521_;
goto v___jp_2512_;
}
default: 
{
v_a_2508_ = v_b_2506_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v___x_2522_; 
lean_dec_ref(v_f_2502_);
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2506_);
return v___x_2522_;
}
v___jp_2507_:
{
size_t v___x_2509_; size_t v___x_2510_; 
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2504_, v___x_2509_);
v_i_2504_ = v___x_2510_;
v_b_2506_ = v_a_2508_;
goto _start;
}
v___jp_2512_:
{
if (lean_obj_tag(v___y_2513_) == 0)
{
lean_dec_ref(v_f_2502_);
return v___y_2513_;
}
else
{
lean_object* v_a_2514_; 
v_a_2514_ = lean_ctor_get(v___y_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___y_2513_, 1);
v_a_2508_ = v_a_2514_;
goto v___jp_2507_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2502_ = stack[0].m_obj;
lean_object* v_as_2503_ = stack[1].m_obj;
size_t v_i_2504_ = stack[2].m_num;
size_t v_stop_2505_ = stack[3].m_num;
lean_object* v_b_2506_ = stack[4].m_obj;
lean_object* v_res_2523_;
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2502_, v_as_2503_, v_i_2504_, v_stop_2505_, v_b_2506_);
stack->m_obj
 = v_res_2523_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_){
_start:
{
if (lean_obj_tag(v_x_2525_) == 0)
{
lean_object* v_es_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2540_; 
v_es_2527_ = lean_ctor_get(v_x_2525_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_x_2525_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2529_ = v_x_2525_;
v_isShared_2530_ = v_isSharedCheck_2540_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_es_2527_);
lean_dec(v_x_2525_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2540_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_array_get_size(v_es_2527_);
v___x_2533_ = lean_nat_dec_lt(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2535_; 
lean_dec_ref(v_es_2527_);
lean_dec_ref(v_f_2524_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 1);
lean_ctor_set(v___x_2529_, 0, v_x_2526_);
v___x_2535_ = v___x_2529_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_x_2526_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
else
{
size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
lean_del_object(v___x_2529_);
v___x_2537_ = ((size_t)0ULL);
v___x_2538_ = lean_usize_of_nat(v___x_2532_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2524_, v_es_2527_, v___x_2537_, v___x_2538_, v_x_2526_);
lean_dec_ref(v_es_2527_);
return v___x_2539_;
}
}
}
else
{
lean_object* v_ks_2541_; lean_object* v_vs_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_ks_2541_ = lean_ctor_get(v_x_2525_, 0);
lean_inc_ref(v_ks_2541_);
v_vs_2542_ = lean_ctor_get(v_x_2525_, 1);
lean_inc_ref(v_vs_2542_);
lean_dec_ref_known(v_x_2525_, 2);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2524_, v_ks_2541_, v_vs_2542_, v___x_2543_, v_x_2526_);
lean_dec_ref(v_vs_2542_);
lean_dec_ref(v_ks_2541_);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_2545_, lean_object* v_as_2546_, lean_object* v_i_2547_, lean_object* v_stop_2548_, lean_object* v_b_2549_){
_start:
{
size_t v_i_boxed_2550_; size_t v_stop_boxed_2551_; lean_object* v_res_2552_; 
v_i_boxed_2550_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_stop_boxed_2551_ = lean_unbox_usize(v_stop_2548_);
lean_dec(v_stop_2548_);
v_res_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2545_, v_as_2546_, v_i_boxed_2550_, v_stop_boxed_2551_, v_b_2549_);
lean_dec_ref(v_as_2546_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_2553_, lean_object* v_s_2554_, lean_object* v_a_2555_, lean_object* v_b_2556_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_a_2555_);
lean_ctor_set(v___x_2557_, 1, v_b_2556_);
v___x_2558_ = lean_apply_2(v_f_2553_, v___x_2557_, v_s_2554_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
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
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_a_2567_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2558_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2558_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_2575_, lean_object* v_init_2576_, lean_object* v_f_2577_){
_start:
{
lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v_a_2580_; 
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2578_, 0, v_f_2577_);
lean_inc_ref(v_map_2575_);
v___x_2579_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_2578_, v_map_2575_, v_init_2576_);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref(v___x_2579_);
return v_a_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_2581_, lean_object* v_init_2582_, lean_object* v_f_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2581_, v_init_2582_, v_f_2583_);
lean_dec_ref(v_map_2581_);
return v_res_2584_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_2587_, lean_object* v_a_2588_, uint8_t v___x_2589_, lean_object* v_as_x27_2590_, lean_object* v_b_2591_){
_start:
{
if (lean_obj_tag(v_as_x27_2590_) == 0)
{
lean_dec(v_a_2588_);
lean_dec_ref(v_tactics_2587_);
return v_b_2591_;
}
else
{
lean_object* v_head_2592_; lean_object* v_fst_2593_; lean_object* v_info_2594_; lean_object* v_tail_2595_; lean_object* v_collectKinds_2596_; lean_object* v___x_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_head_2592_ = lean_ctor_get(v_as_x27_2590_, 0);
v_fst_2593_ = lean_ctor_get(v_head_2592_, 0);
v_info_2594_ = lean_ctor_get(v_fst_2593_, 0);
v_tail_2595_ = lean_ctor_get(v_as_x27_2590_, 1);
v_collectKinds_2596_ = lean_ctor_get(v_info_2594_, 1);
v___x_2597_ = lean_box(v___x_2589_);
lean_inc(v_a_2588_);
lean_inc_ref(v_tactics_2587_);
v___f_2598_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2598_, 0, v_tactics_2587_);
lean_closure_set(v___f_2598_, 1, v_a_2588_);
lean_closure_set(v___f_2598_, 2, v___x_2597_);
v___x_2599_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_2596_);
v___x_2600_ = lean_apply_1(v_collectKinds_2596_, v___x_2599_);
v___x_2601_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_2600_, v_b_2591_, v___f_2598_);
lean_dec_ref(v___x_2600_);
v_as_x27_2590_ = v_tail_2595_;
v_b_2591_ = v___x_2601_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tactics_2587_ = stack[0].m_obj;
lean_object* v_a_2588_ = stack[1].m_obj;
uint8_t v___x_2589_ = stack[2].m_num;
lean_object* v_as_x27_2590_ = stack[3].m_obj;
lean_object* v_b_2591_ = stack[4].m_obj;
lean_object* v_res_2603_;
v_res_2603_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2587_, v_a_2588_, v___x_2589_, v_as_x27_2590_, v_b_2591_);
stack->m_obj
 = v_res_2603_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_2604_, lean_object* v_a_2605_, lean_object* v___x_2606_, lean_object* v_as_x27_2607_, lean_object* v_b_2608_){
_start:
{
uint8_t v___x_4497__boxed_2609_; lean_object* v_res_2610_; 
v___x_4497__boxed_2609_ = lean_unbox(v___x_2606_);
v_res_2610_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2604_, v_a_2605_, v___x_4497__boxed_2609_, v_as_x27_2607_, v_b_2608_);
lean_dec(v_as_x27_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_2613_, lean_object* v_init_2614_, lean_object* v_x_2615_){
_start:
{
if (lean_obj_tag(v_x_2615_) == 0)
{
lean_object* v_k_2616_; lean_object* v_v_2617_; lean_object* v_l_2618_; lean_object* v_r_2619_; lean_object* v___x_2620_; lean_object* v_a_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_k_2616_ = lean_ctor_get(v_x_2615_, 1);
lean_inc(v_k_2616_);
v_v_2617_ = lean_ctor_get(v_x_2615_, 2);
lean_inc(v_v_2617_);
v_l_2618_ = lean_ctor_get(v_x_2615_, 3);
lean_inc(v_l_2618_);
v_r_2619_ = lean_ctor_get(v_x_2615_, 4);
lean_inc(v_r_2619_);
lean_dec_ref_known(v_x_2615_, 5);
lean_inc_ref(v_tactics_2613_);
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2613_, v_init_2614_, v_l_2618_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v___x_2622_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0));
v___x_2623_ = lean_name_eq(v_k_2616_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
lean_inc(v_a_2621_);
lean_dec_ref(v___x_2620_);
lean_inc_ref(v_tactics_2613_);
v___x_2624_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2613_, v_k_2616_, v___x_2623_, v_v_2617_, v_a_2621_);
lean_dec(v_v_2617_);
v_init_2614_ = v___x_2624_;
v_x_2615_ = v_r_2619_;
goto _start;
}
else
{
lean_object* v_a_2626_; 
lean_dec(v_v_2617_);
lean_dec(v_k_2616_);
v_a_2626_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2626_);
lean_dec_ref(v___x_2620_);
v_init_2614_ = v_a_2626_;
v_x_2615_ = v_r_2619_;
goto _start;
}
}
else
{
lean_object* v___x_2628_; 
lean_dec_ref(v_tactics_2613_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_init_2614_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_2629_, lean_object* v_table_2630_, lean_object* v_firsts_2631_){
_start:
{
lean_object* v___x_2632_; lean_object* v_a_2633_; 
v___x_2632_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2629_, v_firsts_2631_, v_table_2630_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2632_);
return v_a_2633_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_2634_, lean_object* v_x_2635_, lean_object* v_x_2636_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2635_, v_x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2635_ = stack[1].m_obj;
lean_object* v_x_2636_ = stack[2].m_obj;
uint8_t v_res_2638_;
v_res_2638_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_box(0), v_x_2635_, v_x_2636_);
stack->m_num = v_res_2638_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_){
_start:
{
uint8_t v_res_2642_; lean_object* v_r_2643_; 
v_res_2642_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_2639_, v_x_2640_, v_x_2641_);
lean_dec(v_x_2641_);
lean_dec_ref(v_x_2640_);
v_r_2643_ = lean_box(v_res_2642_);
return v_r_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_2644_, lean_object* v_k_2645_, lean_object* v_t_2646_, lean_object* v_hl_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2644_, v_k_2645_, v_t_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_2649_, lean_object* v_00_u03b2_2650_, lean_object* v_map_2651_, lean_object* v_init_2652_, lean_object* v_f_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2651_, v_init_2652_, v_f_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_2655_, lean_object* v_00_u03b2_2656_, lean_object* v_map_2657_, lean_object* v_init_2658_, lean_object* v_f_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_2655_, v_00_u03b2_2656_, v_map_2657_, v_init_2658_, v_f_2659_);
lean_dec_ref(v_map_2657_);
return v_res_2660_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_2661_, lean_object* v_a_2662_, uint8_t v___x_2663_, lean_object* v_as_2664_, lean_object* v_as_x27_2665_, lean_object* v_b_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2661_, v_a_2662_, v___x_2663_, v_as_x27_2665_, v_b_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_tactics_2661_ = stack[0].m_obj;
lean_object* v_a_2662_ = stack[1].m_obj;
uint8_t v___x_2663_ = stack[2].m_num;
lean_object* v_as_2664_ = stack[3].m_obj;
lean_object* v_as_x27_2665_ = stack[4].m_obj;
lean_object* v_b_2666_ = stack[5].m_obj;
lean_object* v_res_2669_;
v_res_2669_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2661_, v_a_2662_, v___x_2663_, v_as_2664_, v_as_x27_2665_, v_b_2666_, lean_box(0));
stack->m_obj
 = v_res_2669_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_2670_, lean_object* v_a_2671_, lean_object* v___x_2672_, lean_object* v_as_2673_, lean_object* v_as_x27_2674_, lean_object* v_b_2675_, lean_object* v_a_2676_){
_start:
{
uint8_t v___x_4616__boxed_2677_; lean_object* v_res_2678_; 
v___x_4616__boxed_2677_ = lean_unbox(v___x_2672_);
v_res_2678_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2670_, v_a_2671_, v___x_4616__boxed_2677_, v_as_2673_, v_as_x27_2674_, v_b_2675_, v_a_2676_);
lean_dec(v_as_x27_2674_);
lean_dec(v_as_2673_);
return v_res_2678_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_2679_, lean_object* v_x_2680_, size_t v_x_2681_, lean_object* v_x_2682_){
_start:
{
uint8_t v___x_2683_; 
v___x_2683_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2680_, v_x_2681_, v_x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2680_ = stack[1].m_obj;
size_t v_x_2681_ = stack[2].m_num;
lean_object* v_x_2682_ = stack[3].m_obj;
uint8_t v_res_2684_;
v_res_2684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_box(0), v_x_2680_, v_x_2681_, v_x_2682_);
stack->m_num = v_res_2684_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
size_t v_x_4630__boxed_2689_; uint8_t v_res_2690_; lean_object* v_r_2691_; 
v_x_4630__boxed_2689_ = lean_unbox_usize(v_x_2687_);
lean_dec(v_x_2687_);
v_res_2690_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_2685_, v_x_2686_, v_x_4630__boxed_2689_, v_x_2688_);
lean_dec(v_x_2688_);
lean_dec_ref(v_x_2686_);
v_r_2691_ = lean_box(v_res_2690_);
return v_r_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_2692_, lean_object* v_f_2693_, lean_object* v_init_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2693_, v_map_2692_, v_init_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_2696_, lean_object* v_00_u03c3_2697_, lean_object* v_00_u03b2_2698_, lean_object* v_map_2699_, lean_object* v_f_2700_, lean_object* v_init_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2700_, v_map_2699_, v_init_2701_);
return v___x_2702_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2703_, lean_object* v_keys_2704_, lean_object* v_vals_2705_, lean_object* v_heq_2706_, lean_object* v_i_2707_, lean_object* v_k_2708_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2704_, v_i_2707_, v_k_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2704_ = stack[1].m_obj;
lean_object* v_vals_2705_ = stack[2].m_obj;
lean_object* v_i_2707_ = stack[4].m_obj;
lean_object* v_k_2708_ = stack[5].m_obj;
uint8_t v_res_2710_;
v_res_2710_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_box(0), v_keys_2704_, v_vals_2705_, lean_box(0), v_i_2707_, v_k_2708_);
stack->m_num = v_res_2710_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2711_, lean_object* v_keys_2712_, lean_object* v_vals_2713_, lean_object* v_heq_2714_, lean_object* v_i_2715_, lean_object* v_k_2716_){
_start:
{
uint8_t v_res_2717_; lean_object* v_r_2718_; 
v_res_2717_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_2711_, v_keys_2712_, v_vals_2713_, v_heq_2714_, v_i_2715_, v_k_2716_);
lean_dec(v_k_2716_);
lean_dec_ref(v_vals_2713_);
lean_dec_ref(v_keys_2712_);
v_r_2718_ = lean_box(v_res_2717_);
return v_r_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_2719_, lean_object* v_00_u03c3_2720_, lean_object* v_00_u03b1_2721_, lean_object* v_00_u03b2_2722_, lean_object* v_f_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2723_, v_x_2724_, v_x_2725_);
return v___x_2726_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_2727_, lean_object* v_00_u03b2_2728_, lean_object* v_00_u03c3_2729_, lean_object* v_00_u03c3_2730_, lean_object* v_f_2731_, lean_object* v_as_2732_, size_t v_i_2733_, size_t v_stop_2734_, lean_object* v_b_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2731_, v_as_2732_, v_i_2733_, v_stop_2734_, v_b_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2731_ = stack[4].m_obj;
lean_object* v_as_2732_ = stack[5].m_obj;
size_t v_i_2733_ = stack[6].m_num;
size_t v_stop_2734_ = stack[7].m_num;
lean_object* v_b_2735_ = stack[8].m_obj;
lean_object* v_res_2737_;
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_2731_, v_as_2732_, v_i_2733_, v_stop_2734_, v_b_2735_);
stack->m_obj
 = v_res_2737_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_00_u03b2_2739_, lean_object* v_00_u03c3_2740_, lean_object* v_00_u03c3_2741_, lean_object* v_f_2742_, lean_object* v_as_2743_, lean_object* v_i_2744_, lean_object* v_stop_2745_, lean_object* v_b_2746_){
_start:
{
size_t v_i_boxed_2747_; size_t v_stop_boxed_2748_; lean_object* v_res_2749_; 
v_i_boxed_2747_ = lean_unbox_usize(v_i_2744_);
lean_dec(v_i_2744_);
v_stop_boxed_2748_ = lean_unbox_usize(v_stop_2745_);
lean_dec(v_stop_2745_);
v_res_2749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_2738_, v_00_u03b2_2739_, v_00_u03c3_2740_, v_00_u03c3_2741_, v_f_2742_, v_as_2743_, v_i_boxed_2747_, v_stop_boxed_2748_, v_b_2746_);
lean_dec_ref(v_as_2743_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_2750_, lean_object* v_00_u03c3_2751_, lean_object* v_00_u03b1_2752_, lean_object* v_00_u03b2_2753_, lean_object* v_f_2754_, lean_object* v_keys_2755_, lean_object* v_vals_2756_, lean_object* v_heq_2757_, lean_object* v_i_2758_, lean_object* v_acc_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2754_, v_keys_2755_, v_vals_2756_, v_i_2758_, v_acc_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_2761_, lean_object* v_00_u03c3_2762_, lean_object* v_00_u03b1_2763_, lean_object* v_00_u03b2_2764_, lean_object* v_f_2765_, lean_object* v_keys_2766_, lean_object* v_vals_2767_, lean_object* v_heq_2768_, lean_object* v_i_2769_, lean_object* v_acc_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_2761_, v_00_u03c3_2762_, v_00_u03b1_2763_, v_00_u03b2_2764_, v_f_2765_, v_keys_2766_, v_vals_2767_, v_heq_2768_, v_i_2769_, v_acc_2770_);
lean_dec_ref(v_vals_2767_);
lean_dec_ref(v_keys_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_2772_, lean_object* v_x2_2773_){
_start:
{
lean_object* v_fst_2774_; lean_object* v_snd_2775_; lean_object* v___x_2776_; 
v_fst_2774_ = lean_ctor_get(v_x2_2773_, 0);
lean_inc(v_fst_2774_);
v_snd_2775_ = lean_ctor_get(v_x2_2773_, 1);
lean_inc(v_snd_2775_);
lean_dec_ref(v_x2_2773_);
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2774_, v_snd_2775_, v_x1_2772_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_2796_, lean_object* v_x1_2797_, lean_object* v_x2_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_array_get_size(v_x2_2798_);
v___x_2801_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2802_ = lean_nat_dec_lt(v___x_2799_, v___x_2800_);
if (v___x_2802_ == 0)
{
lean_dec_ref(v_x2_2798_);
lean_dec_ref(v___f_2796_);
return v_x1_2797_;
}
else
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_nat_dec_le(v___x_2800_, v___x_2800_);
if (v___x_2803_ == 0)
{
if (v___x_2802_ == 0)
{
lean_dec_ref(v_x2_2798_);
lean_dec_ref(v___f_2796_);
return v_x1_2797_;
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2800_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2801_, v___f_2796_, v_x2_2798_, v___x_2804_, v___x_2805_, v_x1_2797_);
return v___x_2806_;
}
}
else
{
size_t v___x_2807_; size_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = ((size_t)0ULL);
v___x_2808_ = lean_usize_of_nat(v___x_2800_);
v___x_2809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2801_, v___f_2796_, v_x2_2798_, v___x_2807_, v___x_2808_, v_x1_2797_);
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v_toPure_2818_, lean_object* v___f_2819_, lean_object* v_env_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v_ext_2822_; lean_object* v_toEnvExtension_2823_; lean_object* v_asyncMode_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v_categories_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2821_ = l_Lean_Parser_parserExtension;
v_ext_2822_ = lean_ctor_get(v___x_2821_, 1);
v_toEnvExtension_2823_ = lean_ctor_get(v_ext_2822_, 0);
v_asyncMode_2824_ = lean_ctor_get(v_toEnvExtension_2823_, 2);
v___x_2825_ = 0;
lean_inc_ref(v_env_2820_);
v___x_2826_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2813_, v___x_2821_, v_env_2820_, v_asyncMode_2824_, v___x_2825_);
v_categories_2827_ = lean_ctor_get(v___x_2826_, 2);
lean_inc_ref(v_categories_2827_);
lean_dec(v___x_2826_);
v___x_2828_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2829_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2814_, v___x_2815_, v_categories_2827_, v___x_2828_);
lean_dec_ref(v_categories_2827_);
if (lean_obj_tag(v___x_2829_) == 1)
{
lean_object* v_val_2830_; lean_object* v___y_2832_; lean_object* v___x_2839_; lean_object* v_toEnvExtension_2840_; lean_object* v_exportEntriesFn_2841_; lean_object* v_asyncMode_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v_importedEntries_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_exported_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_val_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2839_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2840_ = lean_ctor_get(v___x_2839_, 0);
v_exportEntriesFn_2841_ = lean_ctor_get(v___x_2839_, 4);
v_asyncMode_2842_ = lean_ctor_get(v_toEnvExtension_2840_, 2);
v___x_2843_ = lean_box(0);
lean_inc_ref_n(v_env_2820_, 2);
v___x_2844_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2816_, v_toEnvExtension_2840_, v_env_2820_, v_asyncMode_2842_, v___x_2843_, v___x_2825_);
v_importedEntries_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_ref(v_importedEntries_2845_);
lean_dec(v___x_2844_);
v___x_2846_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2817_, v___x_2839_, v_env_2820_, v_asyncMode_2842_, v___x_2843_, v___x_2825_);
lean_inc_ref(v_exportEntriesFn_2841_);
v___x_2847_ = lean_apply_2(v_exportEntriesFn_2841_, v_env_2820_, v___x_2846_);
v_exported_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_exported_2848_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = lean_box(1);
v___x_2850_ = lean_array_push(v_importedEntries_2845_, v_exported_2848_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v___x_2852_ = lean_array_get_size(v___x_2850_);
v___x_2853_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2854_ = lean_nat_dec_lt(v___x_2851_, v___x_2852_);
if (v___x_2854_ == 0)
{
lean_dec_ref(v___x_2850_);
lean_dec_ref(v___f_2819_);
v___y_2832_ = v___x_2849_;
goto v___jp_2831_;
}
else
{
uint8_t v___x_2855_; 
v___x_2855_ = lean_nat_dec_le(v___x_2852_, v___x_2852_);
if (v___x_2855_ == 0)
{
if (v___x_2854_ == 0)
{
lean_dec_ref(v___x_2850_);
lean_dec_ref(v___f_2819_);
v___y_2832_ = v___x_2849_;
goto v___jp_2831_;
}
else
{
size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = ((size_t)0ULL);
v___x_2857_ = lean_usize_of_nat(v___x_2852_);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2853_, v___f_2819_, v___x_2850_, v___x_2856_, v___x_2857_, v___x_2849_);
v___y_2832_ = v___x_2858_;
goto v___jp_2831_;
}
}
else
{
size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = lean_usize_of_nat(v___x_2852_);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2853_, v___f_2819_, v___x_2850_, v___x_2859_, v___x_2860_, v___x_2849_);
v___y_2832_ = v___x_2861_;
goto v___jp_2831_;
}
}
v___jp_2831_:
{
lean_object* v_tables_2833_; lean_object* v_leadingTable_2834_; lean_object* v_trailingTable_2835_; lean_object* v_firstTokens_2836_; lean_object* v_firstTokens_2837_; lean_object* v___x_2838_; 
v_tables_2833_ = lean_ctor_get(v_val_2830_, 2);
v_leadingTable_2834_ = lean_ctor_get(v_tables_2833_, 0);
v_trailingTable_2835_ = lean_ctor_get(v_tables_2833_, 2);
lean_inc(v_trailingTable_2835_);
lean_inc(v_leadingTable_2834_);
lean_inc(v_val_2830_);
v_firstTokens_2836_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2830_, v_leadingTable_2834_, v___y_2832_);
v_firstTokens_2837_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2830_, v_trailingTable_2835_, v_firstTokens_2836_);
v___x_2838_ = lean_apply_2(v_toPure_2818_, lean_box(0), v_firstTokens_2837_);
return v___x_2838_;
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec(v___x_2829_);
lean_dec_ref(v_env_2820_);
lean_dec_ref(v___f_2819_);
lean_dec(v___x_2817_);
v___x_2862_ = lean_box(1);
v___x_2863_ = lean_apply_2(v_toPure_2818_, lean_box(0), v___x_2862_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v_toPure_2869_, lean_object* v___f_2870_, lean_object* v_env_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_2864_, v___x_2865_, v___x_2866_, v___x_2867_, v___x_2868_, v_toPure_2869_, v___f_2870_, v_env_2871_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2864_);
return v_res_2872_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_box(1);
v___x_2877_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_2880_, lean_object* v_inst_2881_){
_start:
{
lean_object* v_toApplicative_2882_; lean_object* v_toBind_2883_; lean_object* v_getEnv_2884_; lean_object* v_toPure_2885_; lean_object* v___f_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___f_2892_; lean_object* v___x_2893_; 
v_toApplicative_2882_ = lean_ctor_get(v_inst_2880_, 0);
lean_inc_ref(v_toApplicative_2882_);
v_toBind_2883_ = lean_ctor_get(v_inst_2880_, 1);
lean_inc(v_toBind_2883_);
lean_dec_ref(v_inst_2880_);
v_getEnv_2884_ = lean_ctor_get(v_inst_2881_, 0);
lean_inc(v_getEnv_2884_);
lean_dec_ref(v_inst_2881_);
v_toPure_2885_ = lean_ctor_get(v_toApplicative_2882_, 1);
lean_inc(v_toPure_2885_);
lean_dec_ref(v_toApplicative_2882_);
v___f_2886_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_2887_ = lean_box(1);
v___x_2888_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2889_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2890_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_2891_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_2892_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2892_, 0, v___x_2891_);
lean_closure_set(v___f_2892_, 1, v___x_2889_);
lean_closure_set(v___f_2892_, 2, v___x_2890_);
lean_closure_set(v___f_2892_, 3, v___x_2888_);
lean_closure_set(v___f_2892_, 4, v___x_2887_);
lean_closure_set(v___f_2892_, 5, v_toPure_2885_);
lean_closure_set(v___f_2892_, 6, v___f_2886_);
v___x_2893_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v_getEnv_2884_, v___f_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_2895_, v_inst_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2900_ = lean_box(1);
v___x_2901_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_2902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_2903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v___x_2901_);
lean_ctor_set(v___x_2903_, 2, v___x_2900_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_2905_, lean_object* v___y_2906_, lean_object* v_toPure_2907_, lean_object* v_firsts_2908_, lean_object* v_____do__lift_2909_){
_start:
{
lean_object* v___y_2911_; lean_object* v_val_2922_; 
if (lean_obj_tag(v_____do__lift_2909_) == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_2905_);
v___x_2925_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_2924_, v_firsts_2908_, v_n_2905_);
if (lean_obj_tag(v___x_2925_) == 0)
{
uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = 1;
lean_inc(v_n_2905_);
v___x_2927_ = l_Lean_Name_toString(v_n_2905_, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
v___y_2911_ = v___x_2928_;
goto v___jp_2910_;
}
else
{
lean_object* v_val_2929_; 
v_val_2929_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_val_2929_);
lean_dec_ref_known(v___x_2925_, 1);
v_val_2922_ = v_val_2929_;
goto v___jp_2921_;
}
}
else
{
lean_object* v_val_2930_; 
lean_dec(v_firsts_2908_);
v_val_2930_ = lean_ctor_get(v_____do__lift_2909_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v_____do__lift_2909_, 1);
v_val_2922_ = v_val_2930_;
goto v___jp_2921_;
}
v___jp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2912_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_2913_ = l_Lean_Expr_const___override(v_n_2905_, v___y_2906_);
v___x_2914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_2915_ = lean_box(0);
v___x_2916_ = 0;
v___x_2917_ = l_Lean_MessageData_withExprHover(v___y_2911_, v___x_2913_, v___x_2914_, v___x_2915_, v___x_2915_, v___x_2915_, v___x_2916_);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2912_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v___x_2912_);
v___x_2920_ = lean_apply_2(v_toPure_2907_, lean_box(0), v___x_2919_);
return v___x_2920_;
}
v___jp_2921_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_val_2922_);
v___y_2911_ = v___x_2923_;
goto v___jp_2910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_2931_, lean_object* v_toPure_2932_, lean_object* v_firsts_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_toBind_2936_, lean_object* v___x_2937_, lean_object* v___x_2938_, lean_object* v___f_2939_, lean_object* v_env_2940_){
_start:
{
lean_object* v___y_2942_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = l_Lean_Environment_constants(v_env_2940_);
lean_inc(v_n_2931_);
v___x_2947_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_2937_, v___x_2938_, v___x_2946_, v_n_2931_);
lean_dec_ref(v___x_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v___f_2939_);
v___x_2948_ = lean_box(0);
v___y_2942_ = v___x_2948_;
goto v___jp_2941_;
}
else
{
lean_object* v_val_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_val_2949_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_val_2949_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2950_ = l_Lean_ConstantInfo_levelParams(v_val_2949_);
lean_dec(v_val_2949_);
v___x_2951_ = lean_box(0);
v___x_2952_ = l_List_mapTR_loop___redArg(v___f_2939_, v___x_2950_, v___x_2951_);
v___y_2942_ = v___x_2952_;
goto v___jp_2941_;
}
v___jp_2941_:
{
lean_object* v___f_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_inc(v_n_2931_);
v___f_2943_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2943_, 0, v_n_2931_);
lean_closure_set(v___f_2943_, 1, v___y_2942_);
lean_closure_set(v___f_2943_, 2, v_toPure_2932_);
lean_closure_set(v___f_2943_, 3, v_firsts_2933_);
v___x_2944_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_2934_, v_inst_2935_, v_n_2931_);
v___x_2945_ = lean_apply_4(v_toBind_2936_, lean_box(0), lean_box(0), v___x_2944_, v___f_2943_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_firsts_2956_, lean_object* v_n_2957_){
_start:
{
lean_object* v_toApplicative_2958_; lean_object* v_toBind_2959_; lean_object* v_getEnv_2960_; lean_object* v_toPure_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; 
v_toApplicative_2958_ = lean_ctor_get(v_inst_2954_, 0);
v_toBind_2959_ = lean_ctor_get(v_inst_2954_, 1);
lean_inc_n(v_toBind_2959_, 2);
v_getEnv_2960_ = lean_ctor_get(v_inst_2955_, 0);
lean_inc(v_getEnv_2960_);
v_toPure_2961_ = lean_ctor_get(v_toApplicative_2958_, 1);
lean_inc(v_toPure_2961_);
v___f_2962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_2963_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_2965_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_2965_, 0, v_n_2957_);
lean_closure_set(v___f_2965_, 1, v_toPure_2961_);
lean_closure_set(v___f_2965_, 2, v_firsts_2956_);
lean_closure_set(v___f_2965_, 3, v_inst_2954_);
lean_closure_set(v___f_2965_, 4, v_inst_2955_);
lean_closure_set(v___f_2965_, 5, v_toBind_2959_);
lean_closure_set(v___f_2965_, 6, v___x_2963_);
lean_closure_set(v___f_2965_, 7, v___x_2964_);
lean_closure_set(v___f_2965_, 8, v___f_2962_);
v___x_2966_ = lean_apply_4(v_toBind_2959_, lean_box(0), lean_box(0), v_getEnv_2960_, v___f_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_firsts_2970_, lean_object* v_n_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_2968_, v_inst_2969_, v_firsts_2970_, v_n_2971_);
return v___x_2972_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_2976_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2977_;
v_res_2977_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
stack->m_obj
 = v_res_2977_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_2979_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_2983_);
lean_dec_ref(v_s_2983_);
return v_res_2984_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_2985_, lean_object* v_x1_2986_, lean_object* v_x2_2987_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = l_Lean_Name_toString(v_x1_2986_, v___x_2985_);
v___x_2989_ = l_Lean_Name_toString(v_x2_2987_, v___x_2985_);
v___x_2990_ = lean_string_dec_lt(v___x_2988_, v___x_2989_);
lean_dec_ref(v___x_2989_);
lean_dec_ref(v___x_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2985_ = stack[0].m_num;
lean_object* v_x1_2986_ = stack[1].m_obj;
lean_object* v_x2_2987_ = stack[2].m_obj;
uint8_t v_res_2991_;
v_res_2991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2985_, v_x1_2986_, v_x2_2987_);
stack->m_num = v_res_2991_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_2992_, lean_object* v_x1_2993_, lean_object* v_x2_2994_){
_start:
{
uint8_t v___x_16976__boxed_2995_; uint8_t v_res_2996_; lean_object* v_r_2997_; 
v___x_16976__boxed_2995_ = lean_unbox(v___x_2992_);
v_res_2996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16976__boxed_2995_, v_x1_2993_, v_x2_2994_);
v_r_2997_ = lean_box(v_res_2996_);
return v_r_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_2998_, lean_object* v_pivot_2999_, lean_object* v_as_3000_, lean_object* v_i_3001_, lean_object* v_k_3002_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_nat_dec_lt(v_k_3002_, v_hi_2998_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v_k_3002_);
lean_dec(v_pivot_2999_);
v___x_3004_ = lean_array_fswap(v_as_3000_, v_i_3001_, v_hi_2998_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_i_3001_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3006_ = lean_array_fget_borrowed(v_as_3000_, v_k_3002_);
lean_inc(v___x_3006_);
v___x_3007_ = l_Lean_Name_toString(v___x_3006_, v___x_3003_);
lean_inc(v_pivot_2999_);
v___x_3008_ = l_Lean_Name_toString(v_pivot_2999_, v___x_3003_);
v___x_3009_ = lean_string_dec_lt(v___x_3007_, v___x_3008_);
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___x_3007_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_unsigned_to_nat(1u);
v___x_3011_ = lean_nat_add(v_k_3002_, v___x_3010_);
lean_dec(v_k_3002_);
v_k_3002_ = v___x_3011_;
goto _start;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3013_ = lean_array_fswap(v_as_3000_, v_i_3001_, v_k_3002_);
v___x_3014_ = lean_unsigned_to_nat(1u);
v___x_3015_ = lean_nat_add(v_i_3001_, v___x_3014_);
lean_dec(v_i_3001_);
v___x_3016_ = lean_nat_add(v_k_3002_, v___x_3014_);
lean_dec(v_k_3002_);
v_as_3000_ = v___x_3013_;
v_i_3001_ = v___x_3015_;
v_k_3002_ = v___x_3016_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_3018_, lean_object* v_pivot_3019_, lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_k_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_3018_, v_pivot_3019_, v_as_3020_, v_i_3021_, v_k_3022_);
lean_dec(v_hi_3018_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_3024_, lean_object* v_as_3025_, lean_object* v_lo_3026_, lean_object* v_hi_3027_){
_start:
{
lean_object* v___y_3029_; uint8_t v___x_3039_; 
v___x_3039_ = lean_nat_dec_lt(v_lo_3026_, v_hi_3027_);
if (v___x_3039_ == 0)
{
lean_dec(v_lo_3026_);
return v_as_3025_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_mid_3042_; lean_object* v___y_3044_; lean_object* v___y_3050_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3040_ = lean_nat_add(v_lo_3026_, v_hi_3027_);
v___x_3041_ = lean_unsigned_to_nat(1u);
v_mid_3042_ = lean_nat_shiftr(v___x_3040_, v___x_3041_);
lean_dec(v___x_3040_);
v___x_3055_ = lean_array_fget_borrowed(v_as_3025_, v_mid_3042_);
v___x_3056_ = lean_array_fget_borrowed(v_as_3025_, v_lo_3026_);
lean_inc(v___x_3056_);
lean_inc(v___x_3055_);
v___x_3057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_3039_, v___x_3055_, v___x_3056_);
if (v___x_3057_ == 0)
{
v___y_3050_ = v_as_3025_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_array_fswap(v_as_3025_, v_lo_3026_, v_mid_3042_);
v___y_3050_ = v___x_3058_;
goto v___jp_3049_;
}
v___jp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3045_ = lean_array_fget_borrowed(v___y_3044_, v_mid_3042_);
v___x_3046_ = lean_array_fget_borrowed(v___y_3044_, v_hi_3027_);
lean_inc(v___x_3046_);
lean_inc(v___x_3045_);
v___x_3047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_3039_, v___x_3045_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_dec(v_mid_3042_);
v___y_3029_ = v___y_3044_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_array_fswap(v___y_3044_, v_mid_3042_, v_hi_3027_);
lean_dec(v_mid_3042_);
v___y_3029_ = v___x_3048_;
goto v___jp_3028_;
}
}
v___jp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3051_ = lean_array_fget_borrowed(v___y_3050_, v_hi_3027_);
v___x_3052_ = lean_array_fget_borrowed(v___y_3050_, v_lo_3026_);
lean_inc(v___x_3052_);
lean_inc(v___x_3051_);
v___x_3053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_3039_, v___x_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
v___y_3044_ = v___y_3050_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_array_fswap(v___y_3050_, v_lo_3026_, v_hi_3027_);
v___y_3044_ = v___x_3054_;
goto v___jp_3043_;
}
}
}
v___jp_3028_:
{
lean_object* v_pivot_3030_; lean_object* v___x_3031_; lean_object* v_fst_3032_; lean_object* v_snd_3033_; uint8_t v___x_3034_; 
v_pivot_3030_ = lean_array_fget(v___y_3029_, v_hi_3027_);
lean_inc_n(v_lo_3026_, 2);
v___x_3031_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_3027_, v_pivot_3030_, v___y_3029_, v_lo_3026_, v_lo_3026_);
v_fst_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_fst_3032_);
v_snd_3033_ = lean_ctor_get(v___x_3031_, 1);
lean_inc(v_snd_3033_);
lean_dec_ref(v___x_3031_);
v___x_3034_ = lean_nat_dec_le(v_hi_3027_, v_fst_3032_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3024_, v_snd_3033_, v_lo_3026_, v_fst_3032_);
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_add(v_fst_3032_, v___x_3036_);
lean_dec(v_fst_3032_);
v_as_3025_ = v___x_3035_;
v_lo_3026_ = v___x_3037_;
goto _start;
}
else
{
lean_dec(v_fst_3032_);
lean_dec(v_lo_3026_);
return v_snd_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_3059_, lean_object* v_as_3060_, lean_object* v_lo_3061_, lean_object* v_hi_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3059_, v_as_3060_, v_lo_3061_, v_hi_3062_);
lean_dec(v_hi_3062_);
lean_dec(v_n_3059_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_3064_, lean_object* v_x_3065_){
_start:
{
if (lean_obj_tag(v_x_3065_) == 0)
{
lean_object* v_k_3066_; lean_object* v_l_3067_; lean_object* v_r_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_k_3066_ = lean_ctor_get(v_x_3065_, 1);
lean_inc(v_k_3066_);
v_l_3067_ = lean_ctor_get(v_x_3065_, 3);
lean_inc(v_l_3067_);
v_r_3068_ = lean_ctor_get(v_x_3065_, 4);
lean_inc(v_r_3068_);
lean_dec_ref_known(v_x_3065_, 5);
v___x_3069_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_3064_, v_l_3067_);
v___x_3070_ = lean_array_push(v___x_3069_, v_k_3066_);
v_init_3064_ = v___x_3070_;
v_x_3065_ = v_r_3068_;
goto _start;
}
else
{
return v_init_3064_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
if (lean_obj_tag(v_a_3072_) == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = l_List_reverse___redArg(v_a_3073_);
return v___x_3074_;
}
else
{
lean_object* v_head_3075_; lean_object* v_tail_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3085_; 
v_head_3075_ = lean_ctor_get(v_a_3072_, 0);
v_tail_3076_ = lean_ctor_get(v_a_3072_, 1);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3072_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3078_ = v_a_3072_;
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_tail_3076_);
lean_inc(v_head_3075_);
lean_dec(v_a_3072_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = l_Lean_Level_param___override(v_head_3075_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v_a_3073_);
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_a_3073_);
v___x_3082_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
v_a_3072_ = v_tail_3076_;
v_a_3073_ = v___x_3082_;
goto _start;
}
}
}
}
}
uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_3086_, lean_object* v_x2_3087_){
_start:
{
lean_object* v_fst_3088_; lean_object* v_fst_3089_; uint8_t v___x_3090_; 
v_fst_3088_ = lean_ctor_get(v_x1_3086_, 0);
v_fst_3089_ = lean_ctor_get(v_x2_3087_, 0);
v___x_3090_ = l_Lean_Name_quickLt(v_fst_3088_, v_fst_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_3086_ = stack[0].m_obj;
lean_object* v_x2_3087_ = stack[1].m_obj;
uint8_t v_res_3091_;
v_res_3091_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_3086_, v_x2_3087_);
stack->m_num = v_res_3091_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_3092_, lean_object* v_x2_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_3092_, v_x2_3093_);
lean_dec_ref(v_x2_3093_);
lean_dec_ref(v_x1_3092_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_3096_, lean_object* v_k_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_m_3102_; lean_object* v_a_3103_; uint8_t v___x_3104_; 
v___x_3100_ = lean_nat_add(v_x_3098_, v_x_3099_);
v___x_3101_ = lean_unsigned_to_nat(1u);
v_m_3102_ = lean_nat_shiftr(v___x_3100_, v___x_3101_);
lean_dec(v___x_3100_);
v_a_3103_ = lean_array_fget_borrowed(v_as_3096_, v_m_3102_);
v___x_3104_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_3103_, v_k_3097_);
if (v___x_3104_ == 0)
{
uint8_t v___x_3105_; 
lean_dec(v_x_3099_);
v___x_3105_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_3097_, v_a_3103_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; 
lean_dec(v_m_3102_);
lean_dec(v_x_3098_);
lean_inc(v_a_3103_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3103_);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_nat_dec_eq(v_m_3102_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3109_ = lean_nat_sub(v_m_3102_, v___x_3101_);
lean_dec(v_m_3102_);
v___x_3110_ = lean_nat_dec_lt(v___x_3109_, v_x_3098_);
if (v___x_3110_ == 0)
{
v_x_3099_ = v___x_3109_;
goto _start;
}
else
{
lean_object* v___x_3112_; 
lean_dec(v___x_3109_);
lean_dec(v_x_3098_);
v___x_3112_ = lean_box(0);
return v___x_3112_;
}
}
else
{
lean_object* v___x_3113_; 
lean_dec(v_m_3102_);
lean_dec(v_x_3098_);
v___x_3113_ = lean_box(0);
return v___x_3113_;
}
}
}
else
{
lean_object* v___x_3114_; uint8_t v___x_3115_; 
lean_dec(v_x_3098_);
v___x_3114_ = lean_nat_add(v_m_3102_, v___x_3101_);
lean_dec(v_m_3102_);
v___x_3115_ = lean_nat_dec_le(v___x_3114_, v_x_3099_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
lean_dec(v___x_3114_);
lean_dec(v_x_3099_);
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
else
{
v_x_3098_ = v___x_3114_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_3118_, lean_object* v_k_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3118_, v_k_3119_, v_x_3120_, v_x_3121_);
lean_dec_ref(v_k_3119_);
lean_dec_ref(v_as_3118_);
return v_res_3122_;
}
}
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v_env_3131_; lean_object* v___x_3132_; 
v___x_3126_ = lean_box(1);
v___x_3127_ = lean_st_ref_get(v___y_3124_);
v_env_3131_ = lean_ctor_get(v___x_3127_, 0);
lean_inc_ref(v_env_3131_);
lean_dec(v___x_3127_);
v___x_3132_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3131_, v_tac_3123_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v___x_3133_; lean_object* v_toEnvExtension_3134_; lean_object* v_asyncMode_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3133_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3134_ = lean_ctor_get(v___x_3133_, 0);
v_asyncMode_3135_ = lean_ctor_get(v_toEnvExtension_3134_, 2);
v___x_3136_ = lean_box(0);
v___x_3137_ = 0;
v___x_3138_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3126_, v___x_3133_, v_env_3131_, v_asyncMode_3135_, v___x_3136_, v___x_3137_);
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3138_, v_tac_3123_);
lean_dec(v_tac_3123_);
lean_dec(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
else
{
lean_object* v_val_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3169_; 
v_val_3141_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3143_ = v___x_3132_;
v_isShared_3144_ = v_isSharedCheck_3169_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_val_3141_);
lean_dec(v___x_3132_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3169_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; uint8_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3145_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3146_ = 0;
v___x_3147_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3126_, v___x_3145_, v_env_3131_, v_val_3141_, v___x_3146_);
lean_dec(v_val_3141_);
lean_dec_ref(v_env_3131_);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_array_get_size(v___x_3147_);
v___x_3150_ = lean_nat_dec_lt(v___x_3148_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec_ref(v___x_3147_);
lean_del_object(v___x_3143_);
lean_dec(v_tac_3123_);
goto v___jp_3128_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_sub(v___x_3149_, v___x_3151_);
v___x_3153_ = lean_nat_dec_le(v___x_3148_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec(v___x_3152_);
lean_dec_ref(v___x_3147_);
lean_del_object(v___x_3143_);
lean_dec(v_tac_3123_);
goto v___jp_3128_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_tac_3123_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_3147_, v___x_3155_, v___x_3148_, v___x_3152_);
lean_dec_ref_known(v___x_3155_, 2);
lean_dec_ref(v___x_3147_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_del_object(v___x_3143_);
goto v___jp_3128_;
}
else
{
lean_object* v_val_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3168_; 
v_val_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3168_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_val_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3168_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v_snd_3161_; lean_object* v___x_3163_; 
v_snd_3161_ = lean_ctor_get(v_val_3157_, 1);
lean_inc(v_snd_3161_);
lean_dec(v_val_3157_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v_snd_3161_);
v___x_3163_ = v___x_3159_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_snd_3161_);
v___x_3163_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3165_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3163_);
v___x_3165_ = v___x_3143_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
}
}
v___jp_3128_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tac_3123_ = stack[0].m_obj;
lean_object* v___y_3124_ = stack[1].m_obj;
lean_object* v_res_3170_;
v_res_3170_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3123_, v___y_3124_);
stack->m_obj
 = v_res_3170_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3171_, v___y_3172_);
lean_dec(v___y_3172_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_3175_, lean_object* v_k_3176_){
_start:
{
if (lean_obj_tag(v_t_3175_) == 0)
{
lean_object* v_k_3177_; lean_object* v_v_3178_; lean_object* v_l_3179_; lean_object* v_r_3180_; uint8_t v___x_3181_; 
v_k_3177_ = lean_ctor_get(v_t_3175_, 1);
v_v_3178_ = lean_ctor_get(v_t_3175_, 2);
v_l_3179_ = lean_ctor_get(v_t_3175_, 3);
v_r_3180_ = lean_ctor_get(v_t_3175_, 4);
v___x_3181_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3176_, v_k_3177_);
switch(v___x_3181_)
{
case 0:
{
v_t_3175_ = v_l_3179_;
goto _start;
}
case 1:
{
lean_object* v___x_3183_; 
lean_inc(v_v_3178_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v_v_3178_);
return v___x_3183_;
}
default: 
{
v_t_3175_ = v_r_3180_;
goto _start;
}
}
}
else
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_box(0);
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_3186_, lean_object* v_k_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3186_, v_k_3187_);
lean_dec(v_k_3187_);
lean_dec(v_t_3186_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_box(0);
return v___x_3191_;
}
else
{
lean_object* v_key_3192_; lean_object* v_value_3193_; lean_object* v_tail_3194_; uint8_t v___x_3195_; 
v_key_3192_ = lean_ctor_get(v_x_3190_, 0);
v_value_3193_ = lean_ctor_get(v_x_3190_, 1);
v_tail_3194_ = lean_ctor_get(v_x_3190_, 2);
v___x_3195_ = lean_name_eq(v_key_3192_, v_a_3189_);
if (v___x_3195_ == 0)
{
v_x_3190_ = v_tail_3194_;
goto _start;
}
else
{
lean_object* v___x_3197_; 
lean_inc(v_value_3193_);
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v_value_3193_);
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3198_, v_x_3199_);
lean_dec(v_x_3199_);
lean_dec(v_a_3198_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_buckets_3203_; lean_object* v___x_3204_; uint64_t v___y_3206_; 
v_buckets_3203_ = lean_ctor_get(v_m_3201_, 1);
v___x_3204_ = lean_array_get_size(v_buckets_3203_);
if (lean_obj_tag(v_a_3202_) == 0)
{
uint64_t v___x_3220_; 
v___x_3220_ = 1723ULL;
v___y_3206_ = v___x_3220_;
goto v___jp_3205_;
}
else
{
uint64_t v_hash_3221_; 
v_hash_3221_ = lean_ctor_get_uint64(v_a_3202_, sizeof(void*)*2);
v___y_3206_ = v_hash_3221_;
goto v___jp_3205_;
}
v___jp_3205_:
{
uint64_t v___x_3207_; uint64_t v___x_3208_; uint64_t v_fold_3209_; uint64_t v___x_3210_; uint64_t v___x_3211_; uint64_t v___x_3212_; size_t v___x_3213_; size_t v___x_3214_; size_t v___x_3215_; size_t v___x_3216_; size_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3207_ = 32ULL;
v___x_3208_ = lean_uint64_shift_right(v___y_3206_, v___x_3207_);
v_fold_3209_ = lean_uint64_xor(v___y_3206_, v___x_3208_);
v___x_3210_ = 16ULL;
v___x_3211_ = lean_uint64_shift_right(v_fold_3209_, v___x_3210_);
v___x_3212_ = lean_uint64_xor(v_fold_3209_, v___x_3211_);
v___x_3213_ = lean_uint64_to_usize(v___x_3212_);
v___x_3214_ = lean_usize_of_nat(v___x_3204_);
v___x_3215_ = ((size_t)1ULL);
v___x_3216_ = lean_usize_sub(v___x_3214_, v___x_3215_);
v___x_3217_ = lean_usize_land(v___x_3213_, v___x_3216_);
v___x_3218_ = lean_array_uget_borrowed(v_buckets_3203_, v___x_3217_);
v___x_3219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3202_, v___x_3218_);
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_m_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_3225_, lean_object* v_vals_3226_, lean_object* v_i_3227_, lean_object* v_k_3228_){
_start:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = lean_array_get_size(v_keys_3225_);
v___x_3230_ = lean_nat_dec_lt(v_i_3227_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec(v_i_3227_);
v___x_3231_ = lean_box(0);
return v___x_3231_;
}
else
{
lean_object* v_k_x27_3232_; uint8_t v___x_3233_; 
v_k_x27_3232_ = lean_array_fget_borrowed(v_keys_3225_, v_i_3227_);
v___x_3233_ = lean_name_eq(v_k_3228_, v_k_x27_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3235_ = lean_nat_add(v_i_3227_, v___x_3234_);
lean_dec(v_i_3227_);
v_i_3227_ = v___x_3235_;
goto _start;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_array_fget_borrowed(v_vals_3226_, v_i_3227_);
lean_dec(v_i_3227_);
lean_inc(v___x_3237_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_3239_, lean_object* v_vals_3240_, lean_object* v_i_3241_, lean_object* v_k_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3239_, v_vals_3240_, v_i_3241_, v_k_3242_);
lean_dec(v_k_3242_);
lean_dec_ref(v_vals_3240_);
lean_dec_ref(v_keys_3239_);
return v_res_3243_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3244_, size_t v_x_3245_, lean_object* v_x_3246_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 0)
{
lean_object* v_es_3247_; lean_object* v___x_3248_; size_t v___x_3249_; size_t v___x_3250_; lean_object* v_j_3251_; lean_object* v___x_3252_; 
v_es_3247_ = lean_ctor_get(v_x_3244_, 0);
v___x_3248_ = lean_box(2);
v___x_3249_ = ((size_t)31ULL);
v___x_3250_ = lean_usize_land(v_x_3245_, v___x_3249_);
v_j_3251_ = lean_usize_to_nat(v___x_3250_);
v___x_3252_ = lean_array_get_borrowed(v___x_3248_, v_es_3247_, v_j_3251_);
lean_dec(v_j_3251_);
switch(lean_obj_tag(v___x_3252_))
{
case 0:
{
lean_object* v_key_3253_; lean_object* v_val_3254_; uint8_t v___x_3255_; 
v_key_3253_ = lean_ctor_get(v___x_3252_, 0);
v_val_3254_ = lean_ctor_get(v___x_3252_, 1);
v___x_3255_ = lean_name_eq(v_x_3246_, v_key_3253_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_box(0);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; 
lean_inc(v_val_3254_);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_val_3254_);
return v___x_3257_;
}
}
case 1:
{
lean_object* v_node_3258_; size_t v___x_3259_; size_t v___x_3260_; 
v_node_3258_ = lean_ctor_get(v___x_3252_, 0);
v___x_3259_ = ((size_t)5ULL);
v___x_3260_ = lean_usize_shift_right(v_x_3245_, v___x_3259_);
v_x_3244_ = v_node_3258_;
v_x_3245_ = v___x_3260_;
goto _start;
}
default: 
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_box(0);
return v___x_3262_;
}
}
}
else
{
lean_object* v_ks_3263_; lean_object* v_vs_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v_ks_3263_ = lean_ctor_get(v_x_3244_, 0);
v_vs_3264_ = lean_ctor_get(v_x_3244_, 1);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_3263_, v_vs_3264_, v___x_3265_, v_x_3246_);
return v___x_3266_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3244_ = stack[0].m_obj;
size_t v_x_3245_ = stack[1].m_num;
lean_object* v_x_3246_ = stack[2].m_obj;
lean_object* v_res_3267_;
v_res_3267_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3244_, v_x_3245_, v_x_3246_);
stack->m_obj
 = v_res_3267_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
size_t v_x_17537__boxed_3271_; lean_object* v_res_3272_; 
v_x_17537__boxed_3271_ = lean_unbox_usize(v_x_3269_);
lean_dec(v_x_3269_);
v_res_3272_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3268_, v_x_17537__boxed_3271_, v_x_3270_);
lean_dec(v_x_3270_);
lean_dec_ref(v_x_3268_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
uint64_t v___y_3276_; 
if (lean_obj_tag(v_x_3274_) == 0)
{
uint64_t v___x_3279_; 
v___x_3279_ = 1723ULL;
v___y_3276_ = v___x_3279_;
goto v___jp_3275_;
}
else
{
uint64_t v_hash_3280_; 
v_hash_3280_ = lean_ctor_get_uint64(v_x_3274_, sizeof(void*)*2);
v___y_3276_ = v_hash_3280_;
goto v___jp_3275_;
}
v___jp_3275_:
{
size_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = lean_uint64_to_usize(v___y_3276_);
v___x_3278_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3273_, v___x_3277_, v_x_3274_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3281_, v_x_3282_);
lean_dec(v_x_3282_);
lean_dec_ref(v_x_3281_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
uint8_t v_stage_u2081_3286_; 
v_stage_u2081_3286_ = lean_ctor_get_uint8(v_x_3284_, sizeof(void*)*2);
if (v_stage_u2081_3286_ == 0)
{
lean_object* v_map_u2081_3287_; lean_object* v_map_u2082_3288_; lean_object* v___x_3289_; 
v_map_u2081_3287_ = lean_ctor_get(v_x_3284_, 0);
v_map_u2082_3288_ = lean_ctor_get(v_x_3284_, 1);
v___x_3289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3287_, v_x_3285_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_3288_, v_x_3285_);
return v___x_3290_;
}
else
{
return v___x_3289_;
}
}
else
{
lean_object* v_map_u2081_3291_; lean_object* v___x_3292_; 
v_map_u2081_3291_ = lean_ctor_get(v_x_3284_, 0);
v___x_3292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3291_, v_x_3285_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_3293_, lean_object* v_x_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3293_, v_x_3294_);
lean_dec(v_x_3294_);
lean_dec_ref(v_x_3293_);
return v_res_3295_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_3296_, lean_object* v_n_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3316_; lean_object* v_val_3317_; lean_object* v___x_3319_; lean_object* v___y_3321_; lean_object* v_env_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3319_ = lean_st_ref_get(v___y_3299_);
v_env_3336_ = lean_ctor_get(v___x_3319_, 0);
lean_inc_ref(v_env_3336_);
lean_dec(v___x_3319_);
v___x_3337_ = l_Lean_Environment_constants(v_env_3336_);
v___x_3338_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_3337_, v_n_3297_);
lean_dec_ref(v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_box(0);
v___y_3321_ = v___x_3339_;
goto v___jp_3320_;
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_val_3340_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3341_ = l_Lean_ConstantInfo_levelParams(v_val_3340_);
lean_dec(v_val_3340_);
v___x_3342_ = lean_box(0);
v___x_3343_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_3341_, v___x_3342_);
v___y_3321_ = v___x_3343_;
goto v___jp_3320_;
}
v___jp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3304_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_3305_ = l_Lean_Expr_const___override(v_n_3297_, v___y_3302_);
v___x_3306_ = lean_unsigned_to_nat(32u);
v___x_3307_ = lean_mk_empty_array_with_capacity(v___x_3306_);
lean_dec_ref(v___x_3307_);
v___x_3308_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3309_ = lean_box(0);
v___x_3310_ = 0;
v___x_3311_ = l_Lean_MessageData_withExprHover(v___y_3303_, v___x_3305_, v___x_3308_, v___x_3309_, v___x_3309_, v___x_3309_, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3304_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v___x_3304_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
v___jp_3315_:
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_val_3317_);
v___y_3302_ = v___y_3316_;
v___y_3303_ = v___x_3318_;
goto v___jp_3301_;
}
v___jp_3320_:
{
lean_object* v___x_3322_; lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3335_; 
lean_inc(v_n_3297_);
v___x_3322_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_3297_, v___y_3299_);
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3335_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3335_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
if (lean_obj_tag(v_a_3323_) == 0)
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_3296_, v_n_3297_);
if (lean_obj_tag(v___x_3327_) == 0)
{
uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3328_ = 1;
lean_inc(v_n_3297_);
v___x_3329_ = l_Lean_Name_toString(v_n_3297_, v___x_3328_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 3);
lean_ctor_set(v___x_3325_, 0, v___x_3329_);
v___x_3331_ = v___x_3325_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
v___y_3302_ = v___y_3321_;
v___y_3303_ = v___x_3331_;
goto v___jp_3301_;
}
}
else
{
lean_object* v_val_3333_; 
lean_del_object(v___x_3325_);
v_val_3333_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v___x_3327_, 1);
v___y_3316_ = v___y_3321_;
v_val_3317_ = v_val_3333_;
goto v___jp_3315_;
}
}
else
{
lean_object* v_val_3334_; 
lean_del_object(v___x_3325_);
v_val_3334_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v_a_3323_, 1);
v___y_3316_ = v___y_3321_;
v_val_3317_ = v_val_3334_;
goto v___jp_3315_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_firsts_3296_ = stack[0].m_obj;
lean_object* v_n_3297_ = stack[1].m_obj;
lean_object* v___y_3298_ = stack[2].m_obj;
lean_object* v___y_3299_ = stack[3].m_obj;
lean_object* v_res_3344_;
v_res_3344_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3296_, v_n_3297_, v___y_3298_, v___y_3299_);
stack->m_obj
 = v_res_3344_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_3345_, lean_object* v_n_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3345_, v_n_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v_firsts_3345_);
return v_res_3350_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
if (lean_obj_tag(v_x_3352_) == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = l_List_reverse___redArg(v_x_3353_);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
else
{
lean_object* v_head_3359_; lean_object* v_tail_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3378_; 
v_head_3359_ = lean_ctor_get(v_x_3352_, 0);
v_tail_3360_ = lean_ctor_get(v_x_3352_, 1);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_x_3352_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3362_ = v_x_3352_;
v_isShared_3363_ = v_isSharedCheck_3378_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_tail_3360_);
lean_inc(v_head_3359_);
lean_dec(v_x_3352_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3378_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_3351_, v_head_3359_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 1, v_x_3353_);
lean_ctor_set(v___x_3362_, 0, v_a_3365_);
v___x_3367_ = v___x_3362_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3365_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_x_3353_);
v___x_3367_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
v_x_3352_ = v_tail_3360_;
v_x_3353_ = v___x_3367_;
goto _start;
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_del_object(v___x_3362_);
lean_dec(v_tail_3360_);
lean_dec(v_x_3353_);
v_a_3370_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3364_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3364_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3351_ = stack[0].m_obj;
lean_object* v_x_3352_ = stack[1].m_obj;
lean_object* v_x_3353_ = stack[2].m_obj;
lean_object* v___y_3354_ = stack[3].m_obj;
lean_object* v___y_3355_ = stack[4].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3351_, v_x_3352_, v_x_3353_, v___y_3354_, v___y_3355_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3380_, v_x_3381_, v_x_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v_a_3380_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_3387_, lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v_a_3390_, lean_object* v_b_3391_){
_start:
{
lean_object* v_it_3393_; lean_object* v_startInclusive_3394_; lean_object* v_endExclusive_3395_; 
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v_currPos_3400_; lean_object* v_searcher_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3424_; 
v_currPos_3400_ = lean_ctor_get(v_a_3390_, 0);
v_searcher_3401_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3403_ = v_a_3390_;
v_isShared_3404_ = v_isSharedCheck_3424_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_searcher_3401_);
lean_inc(v_currPos_3400_);
lean_dec(v_a_3390_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3424_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint8_t v_decide_3405_; 
v_decide_3405_ = lean_nat_dec_eq(v_searcher_3401_, v___x_3389_);
if (v_decide_3405_ == 0)
{
uint32_t v___x_3406_; uint32_t v___x_3407_; uint8_t v___x_3408_; 
v___x_3406_ = 10;
v___x_3407_ = lean_string_utf8_get_fast(v_val_3387_, v_searcher_3401_);
v___x_3408_ = lean_uint32_dec_eq(v___x_3407_, v___x_3406_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = lean_string_utf8_next_fast(v_val_3387_, v_searcher_3401_);
lean_dec(v_searcher_3401_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v___x_3409_);
v___x_3411_ = v___x_3403_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_currPos_3400_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
v_a_3390_ = v___x_3411_;
goto _start;
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v_slice_3417_; lean_object* v_nextIt_3419_; 
v___x_3414_ = lean_string_utf8_next_fast(v_val_3387_, v_searcher_3401_);
v___x_3415_ = lean_nat_sub(v___x_3414_, v_searcher_3401_);
v___x_3416_ = lean_nat_add(v_searcher_3401_, v___x_3415_);
lean_dec(v___x_3415_);
v_slice_3417_ = l_String_Slice_subslice_x21(v___x_3388_, v_currPos_3400_, v_searcher_3401_);
lean_inc(v___x_3416_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v___x_3416_);
lean_ctor_set(v___x_3403_, 0, v___x_3416_);
v_nextIt_3419_ = v___x_3403_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3416_);
v_nextIt_3419_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v_startInclusive_3420_; lean_object* v_endExclusive_3421_; 
v_startInclusive_3420_ = lean_ctor_get(v_slice_3417_, 0);
lean_inc(v_startInclusive_3420_);
v_endExclusive_3421_ = lean_ctor_get(v_slice_3417_, 1);
lean_inc(v_endExclusive_3421_);
lean_dec_ref(v_slice_3417_);
v_it_3393_ = v_nextIt_3419_;
v_startInclusive_3394_ = v_startInclusive_3420_;
v_endExclusive_3395_ = v_endExclusive_3421_;
goto v___jp_3392_;
}
}
}
else
{
lean_object* v___x_3423_; 
lean_del_object(v___x_3403_);
lean_dec(v_searcher_3401_);
v___x_3423_ = lean_box(1);
lean_inc(v___x_3389_);
v_it_3393_ = v___x_3423_;
v_startInclusive_3394_ = v_currPos_3400_;
v_endExclusive_3395_ = v___x_3389_;
goto v___jp_3392_;
}
}
}
else
{
lean_dec(v___x_3389_);
return v_b_3391_;
}
v___jp_3392_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = lean_string_utf8_extract_fast(v_val_3387_, v_startInclusive_3394_, v_endExclusive_3395_);
lean_dec(v_endExclusive_3395_);
lean_dec(v_startInclusive_3394_);
v___x_3397_ = l_Lean_stringToMessageData(v___x_3396_);
v___x_3398_ = lean_array_push(v_b_3391_, v___x_3397_);
v_a_3390_ = v_it_3393_;
v_b_3391_ = v___x_3398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_3425_, lean_object* v___x_3426_, lean_object* v___x_3427_, lean_object* v_a_3428_, lean_object* v_b_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3425_, v___x_3426_, v___x_3427_, v_a_3428_, v_b_3429_);
lean_dec_ref(v___x_3426_);
lean_dec_ref(v_val_3425_);
return v_res_3430_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
return v___x_3435_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
return v___x_3438_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_3446_ = l_Lean_MessageData_ofFormat(v___x_3445_);
return v___x_3446_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
if (lean_obj_tag(v_x_3449_) == 0)
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = l_List_reverse___redArg(v_x_3450_);
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
else
{
lean_object* v_head_3456_; lean_object* v_tail_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3554_; 
v_head_3456_ = lean_ctor_get(v_x_3449_, 0);
v_tail_3457_ = lean_ctor_get(v_x_3449_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_x_3449_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3459_ = v_x_3449_;
v_isShared_3460_ = v_isSharedCheck_3554_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_tail_3457_);
lean_inc(v_head_3456_);
lean_dec(v_x_3449_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3554_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v_snd_3474_; lean_object* v_fst_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3553_; 
v_snd_3474_ = lean_ctor_get(v_head_3456_, 1);
v_fst_3475_ = lean_ctor_get(v_head_3456_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_head_3456_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3477_ = v_head_3456_;
v_isShared_3478_ = v_isSharedCheck_3553_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_snd_3474_);
lean_inc(v_fst_3475_);
lean_dec(v_head_3456_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3553_;
goto v_resetjp_3476_;
}
v___jp_3461_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___y_3462_);
lean_ctor_set(v___x_3466_, 1, v___y_3465_);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v___y_3464_);
v___x_3468_ = l_Lean_MessageData_nestD(v___x_3467_);
lean_inc_ref(v___y_3463_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___y_3463_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v_x_3450_);
lean_ctor_set(v___x_3459_, 0, v___x_3469_);
v___x_3471_ = v___x_3459_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_x_3450_);
v___x_3471_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
v_x_3449_ = v_tail_3457_;
v_x_3450_ = v___x_3471_;
goto _start;
}
}
v_resetjp_3476_:
{
lean_object* v_fst_3479_; lean_object* v_snd_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3552_; 
v_fst_3479_ = lean_ctor_get(v_snd_3474_, 0);
v_snd_3480_ = lean_ctor_get(v_snd_3474_, 1);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_snd_3474_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3482_ = v_snd_3474_;
v_isShared_3483_ = v_isSharedCheck_3552_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snd_3480_);
lean_inc(v_fst_3479_);
lean_dec(v_snd_3474_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3552_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_a_3507_; lean_object* v___y_3523_; lean_object* v___x_3532_; 
v___x_3532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3448_, v_fst_3475_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_MessageData_nil;
v_a_3507_ = v___x_3533_;
goto v___jp_3506_;
}
else
{
lean_object* v_val_3534_; 
v_val_3534_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v___x_3532_, 1);
if (lean_obj_tag(v_val_3534_) == 0)
{
lean_object* v_size_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_size_3535_ = lean_ctor_get(v_val_3534_, 0);
v___x_3536_ = lean_mk_empty_array_with_capacity(v_size_3535_);
v___x_3537_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_3536_, v_val_3534_);
v___x_3538_ = lean_array_get_size(v___x_3537_);
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_nat_dec_eq(v___x_3538_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___y_3548_; uint8_t v___x_3550_; 
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_nat_sub(v___x_3538_, v___x_3545_);
v___x_3550_ = lean_nat_dec_le(v___x_3543_, v___x_3546_);
if (v___x_3550_ == 0)
{
lean_inc(v___x_3546_);
v___y_3548_ = v___x_3546_;
goto v___jp_3547_;
}
else
{
v___y_3548_ = v___x_3543_;
goto v___jp_3547_;
}
v___jp_3547_:
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_nat_dec_le(v___y_3548_, v___x_3546_);
if (v___x_3549_ == 0)
{
lean_dec(v___x_3546_);
lean_inc(v___y_3548_);
v___y_3540_ = v___y_3548_;
v___y_3541_ = v___y_3548_;
goto v___jp_3539_;
}
else
{
v___y_3540_ = v___y_3548_;
v___y_3541_ = v___x_3546_;
goto v___jp_3539_;
}
}
}
else
{
v___y_3523_ = v___x_3537_;
goto v___jp_3522_;
}
v___jp_3539_:
{
lean_object* v___x_3542_; 
v___x_3542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_3538_, v___x_3537_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
v___y_3523_ = v___x_3542_;
goto v___jp_3522_;
}
}
else
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_MessageData_nil;
v_a_3507_ = v___x_3551_;
goto v___jp_3506_;
}
}
v___jp_3484_:
{
lean_object* v___x_3490_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set_tag(v___x_3482_, 7);
lean_ctor_set(v___x_3482_, 1, v___y_3488_);
lean_ctor_set(v___x_3482_, 0, v___y_3486_);
v___x_3490_ = v___x_3482_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___y_3486_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___y_3488_);
v___x_3490_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
if (lean_obj_tag(v_snd_3480_) == 0)
{
lean_object* v___x_3491_; 
lean_del_object(v___x_3477_);
v___x_3491_ = l_Lean_MessageData_nil;
v___y_3462_ = v___x_3490_;
v___y_3463_ = v___y_3485_;
v___y_3464_ = v___y_3487_;
v___y_3465_ = v___x_3491_;
goto v___jp_3461_;
}
else
{
lean_object* v_val_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
v_val_3492_ = lean_ctor_get(v_snd_3480_, 0);
lean_inc_n(v_val_3492_, 2);
lean_dec_ref_known(v_snd_3480_, 1);
v___x_3493_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_string_utf8_byte_size(v_val_3492_);
v___x_3496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3496_, 0, v_val_3492_);
lean_ctor_set(v___x_3496_, 1, v___x_3494_);
lean_ctor_set(v___x_3496_, 2, v___x_3495_);
v___x_3497_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_3498_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_3499_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3492_, v___x_3496_, v___x_3495_, v___x_3497_, v___x_3498_);
lean_dec_ref_known(v___x_3496_, 3);
lean_dec(v_val_3492_);
v___x_3500_ = lean_array_to_list(v___x_3499_);
v___x_3501_ = l_Lean_MessageData_joinSep(v___x_3500_, v___x_3493_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set_tag(v___x_3477_, 7);
lean_ctor_set(v___x_3477_, 1, v___x_3501_);
lean_ctor_set(v___x_3477_, 0, v___x_3493_);
v___x_3503_ = v___x_3477_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
v___y_3462_ = v___x_3490_;
v___y_3463_ = v___y_3485_;
v___y_3464_ = v___y_3487_;
v___y_3465_ = v___x_3503_;
goto v___jp_3461_;
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3508_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_3509_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
lean_inc(v_fst_3475_);
v___x_3510_ = l_Lean_MessageData_ofName(v_fst_3475_);
v___x_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v___x_3509_);
v___x_3513_ = 1;
v___x_3514_ = l_Lean_Name_toString(v_fst_3475_, v___x_3513_);
v___x_3515_ = lean_string_dec_eq(v___x_3514_, v_fst_3479_);
lean_dec_ref(v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3516_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_3517_ = l_Lean_stringToMessageData(v_fst_3479_);
v___x_3518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___y_3485_ = v___x_3508_;
v___y_3486_ = v___x_3512_;
v___y_3487_ = v_a_3507_;
v___y_3488_ = v___x_3520_;
goto v___jp_3484_;
}
else
{
lean_object* v___x_3521_; 
lean_dec(v_fst_3479_);
v___x_3521_ = l_Lean_MessageData_nil;
v___y_3485_ = v___x_3508_;
v___y_3486_ = v___x_3512_;
v___y_3487_ = v_a_3507_;
v___y_3488_ = v___x_3521_;
goto v___jp_3484_;
}
}
v___jp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = lean_array_to_list(v___y_3523_);
v___x_3525_ = lean_box(0);
v___x_3526_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3447_, v___x_3524_, v___x_3525_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3529_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_3530_ = l_Lean_MessageData_joinSep(v_a_3527_, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3528_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v_a_3507_ = v___x_3531_;
goto v___jp_3506_;
}
else
{
lean_del_object(v___x_3482_);
lean_dec(v_snd_3480_);
lean_dec(v_fst_3479_);
lean_del_object(v___x_3477_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3459_);
lean_dec(v_tail_3457_);
lean_dec(v_x_3450_);
return v___x_3526_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3447_ = stack[0].m_obj;
lean_object* v_a_3448_ = stack[1].m_obj;
lean_object* v_x_3449_ = stack[2].m_obj;
lean_object* v_x_3450_ = stack[3].m_obj;
lean_object* v___y_3451_ = stack[4].m_obj;
lean_object* v___y_3452_ = stack[5].m_obj;
lean_object* v_res_3555_;
v_res_3555_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3447_, v_a_3448_, v_x_3449_, v_x_3450_, v___y_3451_, v___y_3452_);
stack->m_obj
 = v_res_3555_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3556_, v_a_3557_, v_x_3558_, v_x_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v_a_3557_);
lean_dec(v_a_3556_);
return v_res_3563_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_3565_, uint8_t v___y_3566_, lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3567_) == 1)
{
lean_object* v_pre_3568_; 
v_pre_3568_ = lean_ctor_get(v_x_3567_, 0);
if (lean_obj_tag(v_pre_3568_) == 0)
{
lean_object* v_str_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_str_3569_ = lean_ctor_get(v_x_3567_, 1);
v___x_3570_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_3571_ = lean_string_dec_eq(v_str_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
return v___x_3571_;
}
else
{
return v_suppressElabErrors_3565_;
}
}
else
{
return v___y_3566_;
}
}
else
{
return v___y_3566_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_3565_ = stack[0].m_num;
uint8_t v___y_3566_ = stack[1].m_num;
lean_object* v_x_3567_ = stack[2].m_obj;
uint8_t v_res_3572_;
v_res_3572_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_3565_, v___y_3566_, v_x_3567_);
stack->m_num = v_res_3572_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_3573_, lean_object* v___y_3574_, lean_object* v_x_3575_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3576_; uint8_t v___y_18444__boxed_3577_; uint8_t v_res_3578_; lean_object* v_r_3579_; 
v_suppressElabErrors_boxed_3576_ = lean_unbox(v_suppressElabErrors_3573_);
v___y_18444__boxed_3577_ = lean_unbox(v___y_3574_);
v_res_3578_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_3576_, v___y_18444__boxed_3577_, v_x_3575_);
lean_dec(v_x_3575_);
v_r_3579_ = lean_box(v_res_3578_);
return v_r_3579_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_3580_, lean_object* v_msgData_3581_, uint8_t v_severity_3582_, uint8_t v_isSilent_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
uint8_t v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; uint8_t v___y_3653_; uint8_t v___y_3654_; uint8_t v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; uint8_t v___y_3681_; lean_object* v___y_3682_; uint8_t v___y_3683_; uint8_t v___y_3684_; lean_object* v___y_3685_; uint8_t v___y_3689_; uint8_t v___y_3690_; uint8_t v___y_3691_; uint8_t v___x_3706_; uint8_t v___y_3708_; uint8_t v___y_3709_; uint8_t v___y_3710_; uint8_t v___y_3712_; uint8_t v___x_3724_; 
v___x_3706_ = 2;
v___x_3724_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3582_, v___x_3706_);
if (v___x_3724_ == 0)
{
v___y_3712_ = v___x_3724_;
goto v___jp_3711_;
}
else
{
uint8_t v___x_3725_; 
lean_inc_ref(v_msgData_3581_);
v___x_3725_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3581_);
v___y_3712_ = v___x_3725_;
goto v___jp_3711_;
}
v___jp_3587_:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_Elab_Command_getScope___redArg(v___y_3595_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v_currNamespace_3598_; lean_object* v___x_3599_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v_currNamespace_3598_ = lean_ctor_get(v_a_3597_, 2);
lean_inc(v_currNamespace_3598_);
lean_dec(v_a_3597_);
v___x_3599_ = l_Lean_Elab_Command_getScope___redArg(v___y_3595_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3635_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3635_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3635_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v_openDecls_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v_env_3609_; lean_object* v_messages_3610_; lean_object* v_scopes_3611_; lean_object* v_usedQuotCtxts_3612_; lean_object* v_nextMacroScope_3613_; lean_object* v_maxRecDepth_3614_; lean_object* v_ngen_3615_; lean_object* v_auxDeclNGen_3616_; lean_object* v_infoState_3617_; lean_object* v_traceState_3618_; lean_object* v_snapshotTasks_3619_; lean_object* v_prevLinterStates_3620_; lean_object* v_codeQualityEntryTasks_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3634_; 
v_openDecls_3604_ = lean_ctor_get(v_a_3600_, 3);
lean_inc(v_openDecls_3604_);
lean_dec(v_a_3600_);
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v_currNamespace_3598_);
lean_ctor_set(v___x_3605_, 1, v_openDecls_3604_);
v___x_3606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___y_3590_);
lean_inc_ref(v___y_3594_);
lean_inc_ref(v___y_3593_);
v___x_3607_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3607_, 0, v___y_3593_);
lean_ctor_set(v___x_3607_, 1, v___y_3591_);
lean_ctor_set(v___x_3607_, 2, v___y_3589_);
lean_ctor_set(v___x_3607_, 3, v___y_3594_);
lean_ctor_set(v___x_3607_, 4, v___x_3606_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*5, v___y_3592_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*5 + 1, v___y_3588_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*5 + 2, v_isSilent_3583_);
v___x_3608_ = lean_st_ref_take(v___y_3595_);
v_env_3609_ = lean_ctor_get(v___x_3608_, 0);
v_messages_3610_ = lean_ctor_get(v___x_3608_, 1);
v_scopes_3611_ = lean_ctor_get(v___x_3608_, 2);
v_usedQuotCtxts_3612_ = lean_ctor_get(v___x_3608_, 3);
v_nextMacroScope_3613_ = lean_ctor_get(v___x_3608_, 4);
v_maxRecDepth_3614_ = lean_ctor_get(v___x_3608_, 5);
v_ngen_3615_ = lean_ctor_get(v___x_3608_, 6);
v_auxDeclNGen_3616_ = lean_ctor_get(v___x_3608_, 7);
v_infoState_3617_ = lean_ctor_get(v___x_3608_, 8);
v_traceState_3618_ = lean_ctor_get(v___x_3608_, 9);
v_snapshotTasks_3619_ = lean_ctor_get(v___x_3608_, 10);
v_prevLinterStates_3620_ = lean_ctor_get(v___x_3608_, 11);
v_codeQualityEntryTasks_3621_ = lean_ctor_get(v___x_3608_, 12);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3623_ = v___x_3608_;
v_isShared_3624_ = v_isSharedCheck_3634_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3621_);
lean_inc(v_prevLinterStates_3620_);
lean_inc(v_snapshotTasks_3619_);
lean_inc(v_traceState_3618_);
lean_inc(v_infoState_3617_);
lean_inc(v_auxDeclNGen_3616_);
lean_inc(v_ngen_3615_);
lean_inc(v_maxRecDepth_3614_);
lean_inc(v_nextMacroScope_3613_);
lean_inc(v_usedQuotCtxts_3612_);
lean_inc(v_scopes_3611_);
lean_inc(v_messages_3610_);
lean_inc(v_env_3609_);
lean_dec(v___x_3608_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3634_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3625_ = lean_box(0);
v___x_3626_ = l_Lean_MessageLog_add(v___x_3607_, v_messages_3610_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 1, v___x_3626_);
v___x_3628_ = v___x_3623_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_env_3609_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_scopes_3611_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v_usedQuotCtxts_3612_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v_nextMacroScope_3613_);
lean_ctor_set(v_reuseFailAlloc_3633_, 5, v_maxRecDepth_3614_);
lean_ctor_set(v_reuseFailAlloc_3633_, 6, v_ngen_3615_);
lean_ctor_set(v_reuseFailAlloc_3633_, 7, v_auxDeclNGen_3616_);
lean_ctor_set(v_reuseFailAlloc_3633_, 8, v_infoState_3617_);
lean_ctor_set(v_reuseFailAlloc_3633_, 9, v_traceState_3618_);
lean_ctor_set(v_reuseFailAlloc_3633_, 10, v_snapshotTasks_3619_);
lean_ctor_set(v_reuseFailAlloc_3633_, 11, v_prevLinterStates_3620_);
lean_ctor_set(v_reuseFailAlloc_3633_, 12, v_codeQualityEntryTasks_3621_);
v___x_3628_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_st_ref_put(v___y_3595_, v___x_3628_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___x_3625_);
v___x_3631_ = v___x_3602_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3625_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v_currNamespace_3598_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
v_a_3636_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3599_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3599_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
v_a_3644_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3596_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3596_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
v___jp_3652_:
{
lean_object* v_fileName_3658_; lean_object* v_fileMap_3659_; uint8_t v_suppressElabErrors_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___f_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3679_; 
v_fileName_3658_ = lean_ctor_get(v___y_3584_, 0);
v_fileMap_3659_ = lean_ctor_get(v___y_3584_, 1);
v_suppressElabErrors_3660_ = lean_ctor_get_uint8(v___y_3584_, sizeof(void*)*10);
v___x_3661_ = lean_box(v_suppressElabErrors_3660_);
v___x_3662_ = lean_box(v___y_3653_);
v___f_3663_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3663_, 0, v___x_3661_);
lean_closure_set(v___f_3663_, 1, v___x_3662_);
v___x_3664_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3581_);
v___x_3665_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v___x_3664_, v___y_3585_);
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3679_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3679_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_inc_ref_n(v_fileMap_3659_, 2);
v___x_3670_ = l_Lean_FileMap_toPosition(v_fileMap_3659_, v___y_3656_);
lean_dec(v___y_3656_);
v___x_3671_ = l_Lean_FileMap_toPosition(v_fileMap_3659_, v___y_3657_);
lean_dec(v___y_3657_);
v___x_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
v___x_3673_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_suppressElabErrors_3660_ == 0)
{
lean_del_object(v___x_3668_);
lean_dec_ref(v___f_3663_);
v___y_3588_ = v___y_3654_;
v___y_3589_ = v___x_3672_;
v___y_3590_ = v_a_3666_;
v___y_3591_ = v___x_3670_;
v___y_3592_ = v___y_3655_;
v___y_3593_ = v_fileName_3658_;
v___y_3594_ = v___x_3673_;
v___y_3595_ = v___y_3585_;
goto v___jp_3587_;
}
else
{
uint8_t v___x_3674_; 
lean_inc(v_a_3666_);
v___x_3674_ = l_Lean_MessageData_hasTag(v___f_3663_, v_a_3666_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
lean_dec_ref_known(v___x_3672_, 1);
lean_dec_ref(v___x_3670_);
lean_dec(v_a_3666_);
v___x_3675_ = lean_box(0);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3675_);
v___x_3677_ = v___x_3668_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
else
{
lean_del_object(v___x_3668_);
v___y_3588_ = v___y_3654_;
v___y_3589_ = v___x_3672_;
v___y_3590_ = v_a_3666_;
v___y_3591_ = v___x_3670_;
v___y_3592_ = v___y_3655_;
v___y_3593_ = v_fileName_3658_;
v___y_3594_ = v___x_3673_;
v___y_3595_ = v___y_3585_;
goto v___jp_3587_;
}
}
}
}
v___jp_3680_:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Syntax_getTailPos_x3f(v___y_3682_, v___y_3684_);
lean_dec(v___y_3682_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_inc(v___y_3685_);
v___y_3653_ = v___y_3681_;
v___y_3654_ = v___y_3683_;
v___y_3655_ = v___y_3684_;
v___y_3656_ = v___y_3685_;
v___y_3657_ = v___y_3685_;
goto v___jp_3652_;
}
else
{
lean_object* v_val_3687_; 
v_val_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_val_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___y_3653_ = v___y_3681_;
v___y_3654_ = v___y_3683_;
v___y_3655_ = v___y_3684_;
v___y_3656_ = v___y_3685_;
v___y_3657_ = v_val_3687_;
goto v___jp_3652_;
}
}
v___jp_3688_:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Elab_Command_getRef___redArg(v___y_3584_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v_ref_3694_; lean_object* v___x_3695_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v_ref_3694_ = l_Lean_replaceRef(v_ref_3580_, v_a_3693_);
lean_dec(v_a_3693_);
v___x_3695_ = l_Lean_Syntax_getPos_x3f(v_ref_3694_, v___y_3690_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_unsigned_to_nat(0u);
v___y_3681_ = v___y_3689_;
v___y_3682_ = v_ref_3694_;
v___y_3683_ = v___y_3691_;
v___y_3684_ = v___y_3690_;
v___y_3685_ = v___x_3696_;
goto v___jp_3680_;
}
else
{
lean_object* v_val_3697_; 
v_val_3697_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v___x_3695_, 1);
v___y_3681_ = v___y_3689_;
v___y_3682_ = v_ref_3694_;
v___y_3683_ = v___y_3691_;
v___y_3684_ = v___y_3690_;
v___y_3685_ = v_val_3697_;
goto v___jp_3680_;
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v_msgData_3581_);
v_a_3698_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3692_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3692_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
v___jp_3707_:
{
if (v___y_3710_ == 0)
{
v___y_3689_ = v___y_3708_;
v___y_3690_ = v___y_3709_;
v___y_3691_ = v_severity_3582_;
goto v___jp_3688_;
}
else
{
v___y_3689_ = v___y_3708_;
v___y_3690_ = v___y_3709_;
v___y_3691_ = v___x_3706_;
goto v___jp_3688_;
}
}
v___jp_3711_:
{
if (v___y_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_scopes_3715_; lean_object* v___x_3716_; lean_object* v_opts_3717_; uint8_t v___x_3718_; uint8_t v___x_3719_; 
v___x_3713_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3714_ = lean_st_ref_get(v___y_3585_);
v_scopes_3715_ = lean_ctor_get(v___x_3714_, 2);
lean_inc(v_scopes_3715_);
lean_dec(v___x_3714_);
v___x_3716_ = l_List_head_x21___redArg(v___x_3713_, v_scopes_3715_);
lean_dec(v_scopes_3715_);
v_opts_3717_ = lean_ctor_get(v___x_3716_, 1);
lean_inc_ref(v_opts_3717_);
lean_dec(v___x_3716_);
v___x_3718_ = 1;
v___x_3719_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3582_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_dec_ref(v_opts_3717_);
v___y_3708_ = v___y_3712_;
v___y_3709_ = v___y_3712_;
v___y_3710_ = v___x_3719_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = l_Lean_warningAsError;
v___x_3721_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_3717_, v___x_3720_);
lean_dec_ref(v_opts_3717_);
v___y_3708_ = v___y_3712_;
v___y_3709_ = v___y_3712_;
v___y_3710_ = v___x_3721_;
goto v___jp_3707_;
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec_ref(v_msgData_3581_);
v___x_3722_ = lean_box(0);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3580_ = stack[0].m_obj;
lean_object* v_msgData_3581_ = stack[1].m_obj;
uint8_t v_severity_3582_ = stack[2].m_num;
uint8_t v_isSilent_3583_ = stack[3].m_num;
lean_object* v___y_3584_ = stack[4].m_obj;
lean_object* v___y_3585_ = stack[5].m_obj;
lean_object* v_res_3726_;
v_res_3726_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3580_, v_msgData_3581_, v_severity_3582_, v_isSilent_3583_, v___y_3584_, v___y_3585_);
stack->m_obj
 = v_res_3726_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_3727_, lean_object* v_msgData_3728_, lean_object* v_severity_3729_, lean_object* v_isSilent_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_severity_boxed_3734_; uint8_t v_isSilent_boxed_3735_; lean_object* v_res_3736_; 
v_severity_boxed_3734_ = lean_unbox(v_severity_3729_);
v_isSilent_boxed_3735_ = lean_unbox(v_isSilent_3730_);
v_res_3736_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3727_, v_msgData_3728_, v_severity_boxed_3734_, v_isSilent_boxed_3735_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v_ref_3727_);
return v_res_3736_;
}
}
lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_3737_, uint8_t v_severity_3738_, uint8_t v_isSilent_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Elab_Command_getRef___redArg(v___y_3740_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3745_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3745_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_3744_, v_msgData_3737_, v_severity_3738_, v_isSilent_3739_, v___y_3740_, v___y_3741_);
lean_dec(v_a_3744_);
return v___x_3745_;
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v_msgData_3737_);
v_a_3746_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3743_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3743_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3737_ = stack[0].m_obj;
uint8_t v_severity_3738_ = stack[1].m_num;
uint8_t v_isSilent_3739_ = stack[2].m_num;
lean_object* v___y_3740_ = stack[3].m_obj;
lean_object* v___y_3741_ = stack[4].m_obj;
lean_object* v_res_3754_;
v_res_3754_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3737_, v_severity_3738_, v_isSilent_3739_, v___y_3740_, v___y_3741_);
stack->m_obj
 = v_res_3754_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_3755_, lean_object* v_severity_3756_, lean_object* v_isSilent_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
uint8_t v_severity_boxed_3761_; uint8_t v_isSilent_boxed_3762_; lean_object* v_res_3763_; 
v_severity_boxed_3761_ = lean_unbox(v_severity_3756_);
v_isSilent_boxed_3762_ = lean_unbox(v_isSilent_3757_);
v_res_3763_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3755_, v_severity_boxed_3761_, v_isSilent_boxed_3762_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3763_;
}
}
lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
uint8_t v___x_3768_; uint8_t v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = 0;
v___x_3769_ = 0;
v___x_3770_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3764_, v___x_3768_, v___x_3769_, v___y_3765_, v___y_3766_);
return v___x_3770_;
}
}
LEAN_EXPORT void l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3764_ = stack[0].m_obj;
lean_object* v___y_3765_ = stack[1].m_obj;
lean_object* v___y_3766_ = stack[2].m_obj;
lean_object* v_res_3771_;
v_res_3771_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_3764_, v___y_3765_, v___y_3766_);
stack->m_obj
 = v_res_3771_;
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3776_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_3777_, lean_object* v_x_3778_){
_start:
{
if (lean_obj_tag(v_x_3778_) == 0)
{
lean_object* v_k_3780_; lean_object* v_v_3781_; lean_object* v_l_3782_; lean_object* v_r_3783_; lean_object* v___x_3784_; lean_object* v_a_3785_; lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_k_3780_ = lean_ctor_get(v_x_3778_, 1);
lean_inc(v_k_3780_);
v_v_3781_ = lean_ctor_get(v_x_3778_, 2);
lean_inc(v_v_3781_);
v_l_3782_ = lean_ctor_get(v_x_3778_, 3);
lean_inc(v_l_3782_);
v_r_3783_ = lean_ctor_get(v_x_3778_, 4);
lean_inc(v_r_3783_);
lean_dec_ref_known(v_x_3778_, 5);
v___x_3784_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3777_, v_l_3782_);
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref(v___x_3784_);
v_a_3786_ = lean_ctor_get(v_a_3785_, 0);
lean_inc(v_a_3786_);
lean_dec(v_a_3785_);
v___x_3787_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3780_, v_v_3781_, v_a_3786_);
v_init_3777_ = v___x_3787_;
v_x_3778_ = v_r_3783_;
goto _start;
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_init_3777_);
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
return v___x_3790_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3777_ = stack[0].m_obj;
lean_object* v_x_3778_ = stack[1].m_obj;
lean_object* v_res_3791_;
v_res_3791_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3777_, v_x_3778_);
stack->m_obj
 = v_res_3791_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_3792_, lean_object* v_x_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3792_, v_x_3793_);
return v_res_3795_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_3796_, lean_object* v_x1_3797_, lean_object* v_x2_3798_){
_start:
{
lean_object* v_fst_3799_; lean_object* v_fst_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v_fst_3799_ = lean_ctor_get(v_x1_3797_, 0);
lean_inc(v_fst_3799_);
lean_dec_ref(v_x1_3797_);
v_fst_3800_ = lean_ctor_get(v_x2_3798_, 0);
lean_inc(v_fst_3800_);
lean_dec_ref(v_x2_3798_);
v___x_3801_ = l_Lean_Name_toString(v_fst_3799_, v___x_3796_);
v___x_3802_ = l_Lean_Name_toString(v_fst_3800_, v___x_3796_);
v___x_3803_ = lean_string_dec_lt(v___x_3801_, v___x_3802_);
lean_dec_ref(v___x_3802_);
lean_dec_ref(v___x_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3796_ = stack[0].m_num;
lean_object* v_x1_3797_ = stack[1].m_obj;
lean_object* v_x2_3798_ = stack[2].m_obj;
uint8_t v_res_3804_;
v_res_3804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3796_, v_x1_3797_, v_x2_3798_);
stack->m_num = v_res_3804_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_3805_, lean_object* v_x1_3806_, lean_object* v_x2_3807_){
_start:
{
uint8_t v___x_18961__boxed_3808_; uint8_t v_res_3809_; lean_object* v_r_3810_; 
v___x_18961__boxed_3808_ = lean_unbox(v___x_3805_);
v_res_3809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18961__boxed_3808_, v_x1_3806_, v_x2_3807_);
v_r_3810_ = lean_box(v_res_3809_);
return v_r_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_3811_, lean_object* v_pivot_3812_, lean_object* v_as_3813_, lean_object* v_i_3814_, lean_object* v_k_3815_){
_start:
{
uint8_t v___x_3816_; 
v___x_3816_ = lean_nat_dec_lt(v_k_3815_, v_hi_3811_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec(v_k_3815_);
lean_dec_ref(v_pivot_3812_);
v___x_3817_ = lean_array_fswap(v_as_3813_, v_i_3814_, v_hi_3811_);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v_i_3814_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
return v___x_3818_;
}
else
{
lean_object* v___x_3819_; lean_object* v_fst_3820_; lean_object* v_fst_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3819_ = lean_array_fget_borrowed(v_as_3813_, v_k_3815_);
v_fst_3820_ = lean_ctor_get(v___x_3819_, 0);
v_fst_3821_ = lean_ctor_get(v_pivot_3812_, 0);
lean_inc(v_fst_3820_);
v___x_3822_ = l_Lean_Name_toString(v_fst_3820_, v___x_3816_);
lean_inc(v_fst_3821_);
v___x_3823_ = l_Lean_Name_toString(v_fst_3821_, v___x_3816_);
v___x_3824_ = lean_string_dec_lt(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
lean_dec_ref(v___x_3822_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = lean_unsigned_to_nat(1u);
v___x_3826_ = lean_nat_add(v_k_3815_, v___x_3825_);
lean_dec(v_k_3815_);
v_k_3815_ = v___x_3826_;
goto _start;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3828_ = lean_array_fswap(v_as_3813_, v_i_3814_, v_k_3815_);
v___x_3829_ = lean_unsigned_to_nat(1u);
v___x_3830_ = lean_nat_add(v_i_3814_, v___x_3829_);
lean_dec(v_i_3814_);
v___x_3831_ = lean_nat_add(v_k_3815_, v___x_3829_);
lean_dec(v_k_3815_);
v_as_3813_ = v___x_3828_;
v_i_3814_ = v___x_3830_;
v_k_3815_ = v___x_3831_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_3833_, lean_object* v_pivot_3834_, lean_object* v_as_3835_, lean_object* v_i_3836_, lean_object* v_k_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3833_, v_pivot_3834_, v_as_3835_, v_i_3836_, v_k_3837_);
lean_dec(v_hi_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_3839_, lean_object* v_as_3840_, lean_object* v_lo_3841_, lean_object* v_hi_3842_){
_start:
{
lean_object* v___y_3844_; uint8_t v___x_3854_; 
v___x_3854_ = lean_nat_dec_lt(v_lo_3841_, v_hi_3842_);
if (v___x_3854_ == 0)
{
lean_dec(v_lo_3841_);
return v_as_3840_;
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v_mid_3857_; lean_object* v___y_3859_; lean_object* v___y_3865_; lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3855_ = lean_nat_add(v_lo_3841_, v_hi_3842_);
v___x_3856_ = lean_unsigned_to_nat(1u);
v_mid_3857_ = lean_nat_shiftr(v___x_3855_, v___x_3856_);
lean_dec(v___x_3855_);
v___x_3870_ = lean_array_fget_borrowed(v_as_3840_, v_mid_3857_);
v___x_3871_ = lean_array_fget_borrowed(v_as_3840_, v_lo_3841_);
lean_inc(v___x_3871_);
lean_inc(v___x_3870_);
v___x_3872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3854_, v___x_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
v___y_3865_ = v_as_3840_;
goto v___jp_3864_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = lean_array_fswap(v_as_3840_, v_lo_3841_, v_mid_3857_);
v___y_3865_ = v___x_3873_;
goto v___jp_3864_;
}
v___jp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
v___x_3860_ = lean_array_fget_borrowed(v___y_3859_, v_mid_3857_);
v___x_3861_ = lean_array_fget_borrowed(v___y_3859_, v_hi_3842_);
lean_inc(v___x_3861_);
lean_inc(v___x_3860_);
v___x_3862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3854_, v___x_3860_, v___x_3861_);
if (v___x_3862_ == 0)
{
lean_dec(v_mid_3857_);
v___y_3844_ = v___y_3859_;
goto v___jp_3843_;
}
else
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_array_fswap(v___y_3859_, v_mid_3857_, v_hi_3842_);
lean_dec(v_mid_3857_);
v___y_3844_ = v___x_3863_;
goto v___jp_3843_;
}
}
v___jp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3866_ = lean_array_fget_borrowed(v___y_3865_, v_hi_3842_);
v___x_3867_ = lean_array_fget_borrowed(v___y_3865_, v_lo_3841_);
lean_inc(v___x_3867_);
lean_inc(v___x_3866_);
v___x_3868_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3854_, v___x_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
v___y_3859_ = v___y_3865_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_array_fswap(v___y_3865_, v_lo_3841_, v_hi_3842_);
v___y_3859_ = v___x_3869_;
goto v___jp_3858_;
}
}
}
v___jp_3843_:
{
lean_object* v_pivot_3845_; lean_object* v___x_3846_; lean_object* v_fst_3847_; lean_object* v_snd_3848_; uint8_t v___x_3849_; 
v_pivot_3845_ = lean_array_fget(v___y_3844_, v_hi_3842_);
lean_inc_n(v_lo_3841_, 2);
v___x_3846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3842_, v_pivot_3845_, v___y_3844_, v_lo_3841_, v_lo_3841_);
v_fst_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_fst_3847_);
v_snd_3848_ = lean_ctor_get(v___x_3846_, 1);
lean_inc(v_snd_3848_);
lean_dec_ref(v___x_3846_);
v___x_3849_ = lean_nat_dec_le(v_hi_3842_, v_fst_3847_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3839_, v_snd_3848_, v_lo_3841_, v_fst_3847_);
v___x_3851_ = lean_unsigned_to_nat(1u);
v___x_3852_ = lean_nat_add(v_fst_3847_, v___x_3851_);
lean_dec(v_fst_3847_);
v_as_3840_ = v___x_3850_;
v_lo_3841_ = v___x_3852_;
goto _start;
}
else
{
lean_dec(v_fst_3847_);
lean_dec(v_lo_3841_);
return v_snd_3848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_3874_, lean_object* v_as_3875_, lean_object* v_lo_3876_, lean_object* v_hi_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3874_, v_as_3875_, v_lo_3876_, v_hi_3877_);
lean_dec(v_hi_3877_);
lean_dec(v_n_3874_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_3879_, lean_object* v_x_3880_){
_start:
{
if (lean_obj_tag(v_x_3880_) == 0)
{
lean_object* v_k_3881_; lean_object* v_v_3882_; lean_object* v_l_3883_; lean_object* v_r_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_k_3881_ = lean_ctor_get(v_x_3880_, 1);
v_v_3882_ = lean_ctor_get(v_x_3880_, 2);
v_l_3883_ = lean_ctor_get(v_x_3880_, 3);
v_r_3884_ = lean_ctor_get(v_x_3880_, 4);
v___x_3885_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3879_, v_l_3883_);
lean_inc(v_v_3882_);
lean_inc(v_k_3881_);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v_k_3881_);
lean_ctor_set(v___x_3886_, 1, v_v_3882_);
v___x_3887_ = lean_array_push(v___x_3885_, v___x_3886_);
v_init_3879_ = v___x_3887_;
v_x_3880_ = v_r_3884_;
goto _start;
}
else
{
return v_init_3879_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3889_, v_x_3890_);
lean_dec(v_x_3890_);
return v_res_3891_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_3892_, size_t v_sz_3893_, size_t v_i_3894_, lean_object* v_b_3895_){
_start:
{
uint8_t v___x_3897_; 
v___x_3897_ = lean_usize_dec_lt(v_i_3894_, v_sz_3893_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v_b_3895_);
return v___x_3898_;
}
else
{
lean_object* v_a_3899_; lean_object* v_fst_3900_; lean_object* v_snd_3901_; lean_object* v_found_3902_; size_t v___x_3903_; size_t v___x_3904_; 
v_a_3899_ = lean_array_uget_borrowed(v_as_3892_, v_i_3894_);
v_fst_3900_ = lean_ctor_get(v_a_3899_, 0);
v_snd_3901_ = lean_ctor_get(v_a_3899_, 1);
lean_inc(v_snd_3901_);
lean_inc(v_fst_3900_);
v_found_3902_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3900_, v_snd_3901_, v_b_3895_);
v___x_3903_ = ((size_t)1ULL);
v___x_3904_ = lean_usize_add(v_i_3894_, v___x_3903_);
v_i_3894_ = v___x_3904_;
v_b_3895_ = v_found_3902_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3892_ = stack[0].m_obj;
size_t v_sz_3893_ = stack[1].m_num;
size_t v_i_3894_ = stack[2].m_num;
lean_object* v_b_3895_ = stack[3].m_obj;
lean_object* v_res_3906_;
v_res_3906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3892_, v_sz_3893_, v_i_3894_, v_b_3895_);
stack->m_obj
 = v_res_3906_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_3907_, lean_object* v_sz_3908_, lean_object* v_i_3909_, lean_object* v_b_3910_, lean_object* v___y_3911_){
_start:
{
size_t v_sz_boxed_3912_; size_t v_i_boxed_3913_; lean_object* v_res_3914_; 
v_sz_boxed_3912_ = lean_unbox_usize(v_sz_3908_);
lean_dec(v_sz_3908_);
v_i_boxed_3913_ = lean_unbox_usize(v_i_3909_);
lean_dec(v_i_3909_);
v_res_3914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3907_, v_sz_boxed_3912_, v_i_boxed_3913_, v_b_3910_);
lean_dec_ref(v_as_3907_);
return v_res_3914_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3915_, size_t v_sz_3916_, size_t v_i_3917_, lean_object* v_b_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
uint8_t v___x_3922_; 
v___x_3922_ = lean_usize_dec_lt(v_i_3917_, v_sz_3916_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v_b_3918_);
return v___x_3923_;
}
else
{
lean_object* v_a_3924_; size_t v_sz_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v_a_3924_ = lean_array_uget_borrowed(v_as_3915_, v_i_3917_);
v_sz_3925_ = lean_array_size(v_a_3924_);
v___x_3926_ = ((size_t)0ULL);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_3924_, v_sz_3925_, v___x_3926_, v_b_3918_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; size_t v___x_3929_; size_t v___x_3930_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3929_ = ((size_t)1ULL);
v___x_3930_ = lean_usize_add(v_i_3917_, v___x_3929_);
v_i_3917_ = v___x_3930_;
v_b_3918_ = v_a_3928_;
goto _start;
}
else
{
return v___x_3927_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3915_ = stack[0].m_obj;
size_t v_sz_3916_ = stack[1].m_num;
size_t v_i_3917_ = stack[2].m_num;
lean_object* v_b_3918_ = stack[3].m_obj;
lean_object* v___y_3919_ = stack[4].m_obj;
lean_object* v___y_3920_ = stack[5].m_obj;
lean_object* v_res_3932_;
v_res_3932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3915_, v_sz_3916_, v_i_3917_, v_b_3918_, v___y_3919_, v___y_3920_);
stack->m_obj
 = v_res_3932_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3933_, lean_object* v_sz_3934_, lean_object* v_i_3935_, lean_object* v_b_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
size_t v_sz_boxed_3940_; size_t v_i_boxed_3941_; lean_object* v_res_3942_; 
v_sz_boxed_3940_ = lean_unbox_usize(v_sz_3934_);
lean_dec(v_sz_3934_);
v_i_boxed_3941_ = lean_unbox_usize(v_i_3935_);
lean_dec(v_i_3935_);
v_res_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3933_, v_sz_boxed_3940_, v_i_boxed_3941_, v_b_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec_ref(v_as_3933_);
return v_res_3942_;
}
}
lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___y_3949_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_env_3967_; lean_object* v___x_3968_; lean_object* v_toEnvExtension_3969_; lean_object* v_asyncMode_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v_a_3974_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v_a_3999_; lean_object* v_a_4000_; 
v___x_3964_ = lean_box(1);
v___x_3965_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3966_ = lean_st_ref_get(v___y_3946_);
v_env_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc_ref_n(v_env_3967_, 2);
lean_dec(v___x_3966_);
v___x_3968_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_3969_ = lean_ctor_get(v___x_3968_, 0);
v_asyncMode_3970_ = lean_ctor_get(v_toEnvExtension_3969_, 2);
v___x_3971_ = lean_box(0);
v___x_3972_ = 0;
v___x_3997_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3964_, v___x_3968_, v_env_3967_, v_asyncMode_3970_, v___x_3971_, v___x_3972_);
v___x_3998_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_3964_, v___x_3997_);
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v_a_4000_ = lean_ctor_get(v_a_3999_, 0);
lean_inc(v_a_4000_);
lean_dec(v_a_3999_);
v_a_3974_ = v_a_4000_;
goto v___jp_3973_;
v___jp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3950_ = lean_array_to_list(v___y_3949_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
return v___x_3951_;
}
v___jp_3952_:
{
lean_object* v___x_3957_; 
v___x_3957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_3955_, v___y_3953_, v___y_3954_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec(v___y_3955_);
v___y_3949_ = v___x_3957_;
goto v___jp_3948_;
}
v___jp_3958_:
{
uint8_t v___x_3963_; 
v___x_3963_ = lean_nat_dec_le(v___y_3962_, v___y_3960_);
if (v___x_3963_ == 0)
{
lean_dec(v___y_3960_);
lean_inc(v___y_3962_);
v___y_3953_ = v___y_3959_;
v___y_3954_ = v___y_3962_;
v___y_3955_ = v___y_3961_;
v___y_3956_ = v___y_3962_;
goto v___jp_3952_;
}
else
{
v___y_3953_ = v___y_3959_;
v___y_3954_ = v___y_3962_;
v___y_3955_ = v___y_3961_;
v___y_3956_ = v___y_3960_;
goto v___jp_3952_;
}
}
v___jp_3973_:
{
lean_object* v___x_3975_; lean_object* v_importedEntries_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3975_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3965_, v_toEnvExtension_3969_, v_env_3967_, v_asyncMode_3970_, v___x_3971_, v___x_3972_);
v_importedEntries_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc_ref(v_importedEntries_3976_);
lean_dec(v___x_3975_);
v_sz_3977_ = lean_array_size(v_importedEntries_3976_);
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_3976_, v_sz_3977_, v___x_3978_, v_a_3974_, v___y_3945_, v___y_3946_);
lean_dec_ref(v_importedEntries_3976_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v_arr_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = lean_unsigned_to_nat(0u);
v___x_3982_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_3983_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_3982_, v_a_3980_);
lean_dec(v_a_3980_);
v___x_3984_ = lean_array_get_size(v_arr_3983_);
v___x_3985_ = lean_nat_dec_eq(v___x_3984_, v___x_3981_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = lean_nat_sub(v___x_3984_, v___x_3986_);
v___x_3988_ = lean_nat_dec_le(v___x_3981_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_inc(v___x_3987_);
v___y_3959_ = v_arr_3983_;
v___y_3960_ = v___x_3987_;
v___y_3961_ = v___x_3984_;
v___y_3962_ = v___x_3987_;
goto v___jp_3958_;
}
else
{
v___y_3959_ = v_arr_3983_;
v___y_3960_ = v___x_3987_;
v___y_3961_ = v___x_3984_;
v___y_3962_ = v___x_3981_;
goto v___jp_3958_;
}
}
else
{
v___y_3949_ = v_arr_3983_;
goto v___jp_3948_;
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3979_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3979_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3945_ = stack[0].m_obj;
lean_object* v___y_3946_ = stack[1].m_obj;
lean_object* v_res_4001_;
v_res_4001_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_3945_, v___y_3946_);
stack->m_obj
 = v_res_4001_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_4006_, lean_object* v_k_4007_, lean_object* v_fallback_4008_){
_start:
{
if (lean_obj_tag(v_t_4006_) == 0)
{
lean_object* v_k_4009_; lean_object* v_v_4010_; lean_object* v_l_4011_; lean_object* v_r_4012_; uint8_t v___x_4013_; 
v_k_4009_ = lean_ctor_get(v_t_4006_, 1);
v_v_4010_ = lean_ctor_get(v_t_4006_, 2);
v_l_4011_ = lean_ctor_get(v_t_4006_, 3);
v_r_4012_ = lean_ctor_get(v_t_4006_, 4);
v___x_4013_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4007_, v_k_4009_);
switch(v___x_4013_)
{
case 0:
{
v_t_4006_ = v_l_4011_;
goto _start;
}
case 1:
{
lean_inc(v_v_4010_);
return v_v_4010_;
}
default: 
{
v_t_4006_ = v_r_4012_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_4008_);
return v_fallback_4008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_4016_, lean_object* v_k_4017_, lean_object* v_fallback_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4016_, v_k_4017_, v_fallback_4018_);
lean_dec(v_fallback_4018_);
lean_dec(v_k_4017_);
lean_dec(v_t_4016_);
return v_res_4019_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_4020_, size_t v_sz_4021_, size_t v_i_4022_, lean_object* v_b_4023_){
_start:
{
uint8_t v___x_4025_; 
v___x_4025_ = lean_usize_dec_lt(v_i_4022_, v_sz_4021_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_b_4023_);
return v___x_4026_;
}
else
{
lean_object* v_a_4027_; lean_object* v_fst_4028_; lean_object* v_snd_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; size_t v___x_4034_; size_t v___x_4035_; 
v_a_4027_ = lean_array_uget_borrowed(v_as_4020_, v_i_4022_);
v_fst_4028_ = lean_ctor_get(v_a_4027_, 0);
v_snd_4029_ = lean_ctor_get(v_a_4027_, 1);
v___x_4030_ = l_Lean_NameSet_empty;
v___x_4031_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4023_, v_snd_4029_, v___x_4030_);
lean_inc(v_fst_4028_);
v___x_4032_ = l_Lean_NameSet_insert(v___x_4031_, v_fst_4028_);
lean_inc(v_snd_4029_);
v___x_4033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_4029_, v___x_4032_, v_b_4023_);
v___x_4034_ = ((size_t)1ULL);
v___x_4035_ = lean_usize_add(v_i_4022_, v___x_4034_);
v_i_4022_ = v___x_4035_;
v_b_4023_ = v___x_4033_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4020_ = stack[0].m_obj;
size_t v_sz_4021_ = stack[1].m_num;
size_t v_i_4022_ = stack[2].m_num;
lean_object* v_b_4023_ = stack[3].m_obj;
lean_object* v_res_4037_;
v_res_4037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4020_, v_sz_4021_, v_i_4022_, v_b_4023_);
stack->m_obj
 = v_res_4037_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_4038_, lean_object* v_sz_4039_, lean_object* v_i_4040_, lean_object* v_b_4041_, lean_object* v___y_4042_){
_start:
{
size_t v_sz_boxed_4043_; size_t v_i_boxed_4044_; lean_object* v_res_4045_; 
v_sz_boxed_4043_ = lean_unbox_usize(v_sz_4039_);
lean_dec(v_sz_4039_);
v_i_boxed_4044_ = lean_unbox_usize(v_i_4040_);
lean_dec(v_i_4040_);
v_res_4045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4038_, v_sz_boxed_4043_, v_i_boxed_4044_, v_b_4041_);
lean_dec_ref(v_as_4038_);
return v_res_4045_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_4046_, size_t v_sz_4047_, size_t v_i_4048_, lean_object* v_b_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
uint8_t v___x_4053_; 
v___x_4053_ = lean_usize_dec_lt(v_i_4048_, v_sz_4047_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_b_4049_);
return v___x_4054_;
}
else
{
lean_object* v_a_4055_; size_t v_sz_4056_; size_t v___x_4057_; lean_object* v___x_4058_; 
v_a_4055_ = lean_array_uget_borrowed(v_as_4046_, v_i_4048_);
v_sz_4056_ = lean_array_size(v_a_4055_);
v___x_4057_ = ((size_t)0ULL);
v___x_4058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_4055_, v_sz_4056_, v___x_4057_, v_b_4049_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; size_t v___x_4060_; size_t v___x_4061_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v___x_4060_ = ((size_t)1ULL);
v___x_4061_ = lean_usize_add(v_i_4048_, v___x_4060_);
v_i_4048_ = v___x_4061_;
v_b_4049_ = v_a_4059_;
goto _start;
}
else
{
return v___x_4058_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4046_ = stack[0].m_obj;
size_t v_sz_4047_ = stack[1].m_num;
size_t v_i_4048_ = stack[2].m_num;
lean_object* v_b_4049_ = stack[3].m_obj;
lean_object* v___y_4050_ = stack[4].m_obj;
lean_object* v___y_4051_ = stack[5].m_obj;
lean_object* v_res_4063_;
v_res_4063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_4046_, v_sz_4047_, v_i_4048_, v_b_4049_, v___y_4050_, v___y_4051_);
stack->m_obj
 = v_res_4063_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_4064_, lean_object* v_sz_4065_, lean_object* v_i_4066_, lean_object* v_b_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
size_t v_sz_boxed_4071_; size_t v_i_boxed_4072_; lean_object* v_res_4073_; 
v_sz_boxed_4071_ = lean_unbox_usize(v_sz_4065_);
lean_dec(v_sz_4065_);
v_i_boxed_4072_ = lean_unbox_usize(v_i_4066_);
lean_dec(v_i_4066_);
v_res_4073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_4064_, v_sz_boxed_4071_, v_i_boxed_4072_, v_b_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec_ref(v_as_4064_);
return v_res_4073_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_4074_, size_t v_i_4075_, size_t v_stop_4076_, lean_object* v_b_4077_){
_start:
{
uint8_t v___x_4078_; 
v___x_4078_ = lean_usize_dec_eq(v_i_4075_, v_stop_4076_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; lean_object* v_fst_4080_; lean_object* v_snd_4081_; lean_object* v___x_4082_; size_t v___x_4083_; size_t v___x_4084_; 
v___x_4079_ = lean_array_uget_borrowed(v_as_4074_, v_i_4075_);
v_fst_4080_ = lean_ctor_get(v___x_4079_, 0);
v_snd_4081_ = lean_ctor_get(v___x_4079_, 1);
lean_inc(v_snd_4081_);
lean_inc(v_fst_4080_);
v___x_4082_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4080_, v_snd_4081_, v_b_4077_);
v___x_4083_ = ((size_t)1ULL);
v___x_4084_ = lean_usize_add(v_i_4075_, v___x_4083_);
v_i_4075_ = v___x_4084_;
v_b_4077_ = v___x_4082_;
goto _start;
}
else
{
return v_b_4077_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4074_ = stack[0].m_obj;
size_t v_i_4075_ = stack[1].m_num;
size_t v_stop_4076_ = stack[2].m_num;
lean_object* v_b_4077_ = stack[3].m_obj;
lean_object* v_res_4086_;
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_4074_, v_i_4075_, v_stop_4076_, v_b_4077_);
stack->m_obj
 = v_res_4086_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_4087_, lean_object* v_i_4088_, lean_object* v_stop_4089_, lean_object* v_b_4090_){
_start:
{
size_t v_i_boxed_4091_; size_t v_stop_boxed_4092_; lean_object* v_res_4093_; 
v_i_boxed_4091_ = lean_unbox_usize(v_i_4088_);
lean_dec(v_i_4088_);
v_stop_boxed_4092_ = lean_unbox_usize(v_stop_4089_);
lean_dec(v_stop_4089_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_4087_, v_i_boxed_4091_, v_stop_boxed_4092_, v_b_4090_);
lean_dec_ref(v_as_4087_);
return v_res_4093_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_4094_, size_t v_i_4095_, size_t v_stop_4096_, lean_object* v_b_4097_){
_start:
{
lean_object* v___y_4099_; uint8_t v___x_4103_; 
v___x_4103_ = lean_usize_dec_eq(v_i_4095_, v_stop_4096_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4104_ = lean_array_uget_borrowed(v_as_4094_, v_i_4095_);
v___x_4105_ = lean_unsigned_to_nat(0u);
v___x_4106_ = lean_array_get_size(v___x_4104_);
v___x_4107_ = lean_nat_dec_lt(v___x_4105_, v___x_4106_);
if (v___x_4107_ == 0)
{
v___y_4099_ = v_b_4097_;
goto v___jp_4098_;
}
else
{
size_t v___x_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
v___x_4108_ = ((size_t)0ULL);
v___x_4109_ = lean_usize_of_nat(v___x_4106_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_4104_, v___x_4108_, v___x_4109_, v_b_4097_);
v___y_4099_ = v___x_4110_;
goto v___jp_4098_;
}
}
else
{
return v_b_4097_;
}
v___jp_4098_:
{
size_t v___x_4100_; size_t v___x_4101_; 
v___x_4100_ = ((size_t)1ULL);
v___x_4101_ = lean_usize_add(v_i_4095_, v___x_4100_);
v_i_4095_ = v___x_4101_;
v_b_4097_ = v___y_4099_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4094_ = stack[0].m_obj;
size_t v_i_4095_ = stack[1].m_num;
size_t v_stop_4096_ = stack[2].m_num;
lean_object* v_b_4097_ = stack[3].m_obj;
lean_object* v_res_4111_;
v_res_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_4094_, v_i_4095_, v_stop_4096_, v_b_4097_);
stack->m_obj
 = v_res_4111_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_4112_, lean_object* v_i_4113_, lean_object* v_stop_4114_, lean_object* v_b_4115_){
_start:
{
size_t v_i_boxed_4116_; size_t v_stop_boxed_4117_; lean_object* v_res_4118_; 
v_i_boxed_4116_ = lean_unbox_usize(v_i_4113_);
lean_dec(v_i_4113_);
v_stop_boxed_4117_ = lean_unbox_usize(v_stop_4114_);
lean_dec(v_stop_4114_);
v_res_4118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_4112_, v_i_boxed_4116_, v_stop_boxed_4117_, v_b_4115_);
lean_dec_ref(v_as_4112_);
return v_res_4118_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v_env_4125_; lean_object* v___x_4126_; lean_object* v_ext_4127_; lean_object* v_toEnvExtension_4128_; lean_object* v_asyncMode_4129_; uint8_t v___x_4130_; lean_object* v___x_4131_; lean_object* v_categories_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4121_ = lean_box(1);
v___x_4122_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4123_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4124_ = lean_st_ref_get(v___y_4119_);
v_env_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc_ref_n(v_env_4125_, 2);
lean_dec(v___x_4124_);
v___x_4126_ = l_Lean_Parser_parserExtension;
v_ext_4127_ = lean_ctor_get(v___x_4126_, 1);
v_toEnvExtension_4128_ = lean_ctor_get(v_ext_4127_, 0);
v_asyncMode_4129_ = lean_ctor_get(v_toEnvExtension_4128_, 2);
v___x_4130_ = 0;
v___x_4131_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4123_, v___x_4126_, v_env_4125_, v_asyncMode_4129_, v___x_4130_);
v_categories_4132_ = lean_ctor_get(v___x_4131_, 2);
lean_inc_ref(v_categories_4132_);
lean_dec(v___x_4131_);
v___x_4133_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4134_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4132_, v___x_4133_);
lean_dec_ref(v_categories_4132_);
if (lean_obj_tag(v___x_4134_) == 1)
{
lean_object* v_val_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4166_; 
v_val_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4166_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_val_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4166_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___y_4140_; lean_object* v___x_4149_; lean_object* v_toEnvExtension_4150_; lean_object* v_exportEntriesFn_4151_; lean_object* v_asyncMode_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v_importedEntries_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v_exported_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; 
v___x_4149_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4150_ = lean_ctor_get(v___x_4149_, 0);
v_exportEntriesFn_4151_ = lean_ctor_get(v___x_4149_, 4);
v_asyncMode_4152_ = lean_ctor_get(v_toEnvExtension_4150_, 2);
v___x_4153_ = lean_box(0);
lean_inc_ref_n(v_env_4125_, 2);
v___x_4154_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4122_, v_toEnvExtension_4150_, v_env_4125_, v_asyncMode_4152_, v___x_4153_, v___x_4130_);
v_importedEntries_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc_ref(v_importedEntries_4155_);
lean_dec(v___x_4154_);
v___x_4156_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4121_, v___x_4149_, v_env_4125_, v_asyncMode_4152_, v___x_4153_, v___x_4130_);
lean_inc_ref(v_exportEntriesFn_4151_);
v___x_4157_ = lean_apply_2(v_exportEntriesFn_4151_, v_env_4125_, v___x_4156_);
v_exported_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_exported_4158_);
lean_dec_ref(v___x_4157_);
v___x_4159_ = lean_array_push(v_importedEntries_4155_, v_exported_4158_);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = lean_array_get_size(v___x_4159_);
v___x_4162_ = lean_nat_dec_lt(v___x_4160_, v___x_4161_);
if (v___x_4162_ == 0)
{
lean_dec_ref(v___x_4159_);
v___y_4140_ = v___x_4121_;
goto v___jp_4139_;
}
else
{
size_t v___x_4163_; size_t v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = ((size_t)0ULL);
v___x_4164_ = lean_usize_of_nat(v___x_4161_);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4159_, v___x_4163_, v___x_4164_, v___x_4121_);
lean_dec_ref(v___x_4159_);
v___y_4140_ = v___x_4165_;
goto v___jp_4139_;
}
v___jp_4139_:
{
lean_object* v_tables_4141_; lean_object* v_leadingTable_4142_; lean_object* v_trailingTable_4143_; lean_object* v_firstTokens_4144_; lean_object* v_firstTokens_4145_; lean_object* v___x_4147_; 
v_tables_4141_ = lean_ctor_get(v_val_4135_, 2);
v_leadingTable_4142_ = lean_ctor_get(v_tables_4141_, 0);
v_trailingTable_4143_ = lean_ctor_get(v_tables_4141_, 2);
lean_inc(v_trailingTable_4143_);
lean_inc(v_leadingTable_4142_);
lean_inc(v_val_4135_);
v_firstTokens_4144_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4135_, v_leadingTable_4142_, v___y_4140_);
v_firstTokens_4145_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4135_, v_trailingTable_4143_, v_firstTokens_4144_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set_tag(v___x_4137_, 0);
lean_ctor_set(v___x_4137_, 0, v_firstTokens_4145_);
v___x_4147_ = v___x_4137_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_firstTokens_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_object* v___x_4167_; 
lean_dec(v___x_4134_);
lean_dec_ref(v_env_4125_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4121_);
return v___x_4167_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4119_ = stack[0].m_obj;
lean_object* v_res_4168_;
v_res_4168_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4119_);
stack->m_obj
 = v_res_4168_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4169_);
lean_dec(v___y_4169_);
return v_res_4171_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_4174_ = l_Lean_stringToMessageData(v___x_4173_);
return v___x_4174_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v_env_4181_; lean_object* v___x_4182_; lean_object* v_env_4183_; lean_object* v___x_4184_; lean_object* v_env_4185_; lean_object* v___x_4186_; lean_object* v_toEnvExtension_4187_; lean_object* v_exportEntriesFn_4188_; lean_object* v_asyncMode_4189_; lean_object* v___x_4190_; uint8_t v___x_4191_; lean_object* v___x_4192_; lean_object* v_importedEntries_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4245_; 
v___x_4178_ = lean_box(1);
v___x_4179_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4180_ = lean_st_ref_get(v_a_4176_);
v_env_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc_ref(v_env_4181_);
lean_dec(v___x_4180_);
v___x_4182_ = lean_st_ref_get(v_a_4176_);
v_env_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc_ref(v_env_4183_);
lean_dec(v___x_4182_);
v___x_4184_ = lean_st_ref_get(v_a_4176_);
v_env_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc_ref(v_env_4185_);
lean_dec(v___x_4184_);
v___x_4186_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4187_ = lean_ctor_get(v___x_4186_, 0);
v_exportEntriesFn_4188_ = lean_ctor_get(v___x_4186_, 4);
v_asyncMode_4189_ = lean_ctor_get(v_toEnvExtension_4187_, 2);
v___x_4190_ = lean_box(0);
v___x_4191_ = 0;
v___x_4192_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4179_, v_toEnvExtension_4187_, v_env_4181_, v_asyncMode_4189_, v___x_4190_, v___x_4191_);
v_importedEntries_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v___x_4192_, 1);
lean_dec(v_unused_4246_);
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4245_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_importedEntries_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4245_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v_exported_4199_; lean_object* v___x_4200_; size_t v_sz_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
v___x_4197_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4178_, v___x_4186_, v_env_4185_, v_asyncMode_4189_, v___x_4190_, v___x_4191_);
lean_inc_ref(v_exportEntriesFn_4188_);
v___x_4198_ = lean_apply_2(v_exportEntriesFn_4188_, v_env_4183_, v___x_4197_);
v_exported_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_exported_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_array_push(v_importedEntries_4193_, v_exported_4199_);
v_sz_4201_ = lean_array_size(v___x_4200_);
v___x_4202_ = ((size_t)0ULL);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_4200_, v_sz_4201_, v___x_4202_, v___x_4178_, v_a_4175_, v_a_4176_);
lean_dec_ref(v___x_4200_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v_a_4206_; lean_object* v___x_4207_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_4176_);
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
v___x_4207_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_4175_, v_a_4176_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
v___x_4209_ = lean_box(0);
v___x_4210_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_4206_, v_a_4204_, v_a_4208_, v___x_4209_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4204_);
lean_dec(v_a_4206_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
v___x_4212_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_4213_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_4214_ = l_Lean_MessageData_joinSep(v_a_4211_, v___x_4213_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 7);
lean_ctor_set(v___x_4195_, 1, v___x_4214_);
lean_ctor_set(v___x_4195_, 0, v___x_4213_);
v___x_4216_ = v___x_4195_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4213_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4217_ = l_Lean_MessageData_nestD(v___x_4216_);
v___x_4218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4212_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_4218_, v_a_4175_, v_a_4176_);
return v___x_4219_;
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_del_object(v___x_4195_);
v_a_4221_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4210_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4210_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec(v_a_4206_);
lean_dec(v_a_4204_);
lean_del_object(v___x_4195_);
v_a_4229_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4207_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4207_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_del_object(v___x_4195_);
v_a_4237_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4203_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4203_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4175_ = stack[0].m_obj;
lean_object* v_a_4176_ = stack[1].m_obj;
lean_object* v_res_4247_;
v_res_4247_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4175_, v_a_4176_);
stack->m_obj
 = v_res_4247_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
return v_res_4251_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4253_, v_a_4254_);
return v___x_4256_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_elabPrintTacTags_0interp(lean_interpreter_value* stack)
{
lean_object* v___stx_4252_ = stack[0].m_obj;
lean_object* v_a_4253_ = stack[1].m_obj;
lean_object* v_a_4254_ = stack[2].m_obj;
lean_object* v_res_4257_;
v_res_4257_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4252_, v_a_4253_, v_a_4254_);
stack->m_obj
 = v_res_4257_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4258_, v_a_4259_, v_a_4260_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
lean_dec(v___stx_4258_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_4263_, lean_object* v_t_4264_, lean_object* v_k_4265_, lean_object* v_fallback_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4264_, v_k_4265_, v_fallback_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_4268_, lean_object* v_t_4269_, lean_object* v_k_4270_, lean_object* v_fallback_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_4268_, v_t_4269_, v_k_4270_, v_fallback_4271_);
lean_dec(v_fallback_4271_);
lean_dec(v_k_4270_);
lean_dec(v_t_4269_);
return v_res_4272_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_4273_, size_t v_sz_4274_, size_t v_i_4275_, lean_object* v_b_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4273_, v_sz_4274_, v_i_4275_, v_b_4276_);
return v___x_4280_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4273_ = stack[0].m_obj;
size_t v_sz_4274_ = stack[1].m_num;
size_t v_i_4275_ = stack[2].m_num;
lean_object* v_b_4276_ = stack[3].m_obj;
lean_object* v___y_4277_ = stack[4].m_obj;
lean_object* v___y_4278_ = stack[5].m_obj;
lean_object* v_res_4281_;
v_res_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4273_, v_sz_4274_, v_i_4275_, v_b_4276_, v___y_4277_, v___y_4278_);
stack->m_obj
 = v_res_4281_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_4282_, lean_object* v_sz_4283_, lean_object* v_i_4284_, lean_object* v_b_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
size_t v_sz_boxed_4289_; size_t v_i_boxed_4290_; lean_object* v_res_4291_; 
v_sz_boxed_4289_ = lean_unbox_usize(v_sz_4283_);
lean_dec(v_sz_4283_);
v_i_boxed_4290_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_res_4291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4282_, v_sz_boxed_4289_, v_i_boxed_4290_, v_b_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v_as_4282_);
return v_res_4291_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4293_);
return v___x_4295_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4292_ = stack[0].m_obj;
lean_object* v___y_4293_ = stack[1].m_obj;
lean_object* v_res_4296_;
v_res_4296_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4292_, v___y_4293_);
stack->m_obj
 = v_res_4296_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v_inst_4304_, lean_object* v_R_4305_, lean_object* v_a_4306_, lean_object* v_b_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_4301_, v___x_4302_, v___x_4303_, v_a_4306_, v_b_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_4309_, lean_object* v___x_4310_, lean_object* v___x_4311_, lean_object* v_inst_4312_, lean_object* v_R_4313_, lean_object* v_a_4314_, lean_object* v_b_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_4309_, v___x_4310_, v___x_4311_, v_inst_4312_, v_R_4313_, v_a_4314_, v_b_4315_);
lean_dec_ref(v___x_4310_);
lean_dec_ref(v_val_4309_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_4317_, lean_object* v_t_4318_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_4317_, v_t_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_4320_, lean_object* v_as_4321_, lean_object* v_lo_4322_, lean_object* v_hi_4323_, lean_object* v_w_4324_, lean_object* v_hlo_4325_, lean_object* v_hhi_4326_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_4320_, v_as_4321_, v_lo_4322_, v_hi_4323_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_4328_, lean_object* v_as_4329_, lean_object* v_lo_4330_, lean_object* v_hi_4331_, lean_object* v_w_4332_, lean_object* v_hlo_4333_, lean_object* v_hhi_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_4328_, v_as_4329_, v_lo_4330_, v_hi_4331_, v_w_4332_, v_hlo_4333_, v_hhi_4334_);
lean_dec(v_hi_4331_);
lean_dec(v_n_4328_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_4336_, lean_object* v_x_4337_, lean_object* v_x_4338_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_4337_, v_x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4340_, lean_object* v_x_4341_, lean_object* v_x_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_4340_, v_x_4341_, v_x_4342_);
lean_dec(v_x_4342_);
lean_dec_ref(v_x_4341_);
return v_res_4343_;
}
}
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v___x_4348_; 
v___x_4348_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_4344_, v___y_4346_);
return v___x_4348_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_tac_4344_ = stack[0].m_obj;
lean_object* v___y_4345_ = stack[1].m_obj;
lean_object* v___y_4346_ = stack[2].m_obj;
lean_object* v_res_4349_;
v_res_4349_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4344_, v___y_4345_, v___y_4346_);
stack->m_obj
 = v_res_4349_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_4355_, lean_object* v_t_4356_, lean_object* v_k_4357_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_4356_, v_k_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_4359_, lean_object* v_t_4360_, lean_object* v_k_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_4359_, v_t_4360_, v_k_4361_);
lean_dec(v_k_4361_);
lean_dec(v_t_4360_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_4363_, lean_object* v_x_4364_, lean_object* v_x_4365_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_4364_, v_x_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_4367_, lean_object* v_x_4368_, lean_object* v_x_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_4367_, v_x_4368_, v_x_4369_);
lean_dec(v_x_4369_);
lean_dec_ref(v_x_4368_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_4371_, lean_object* v_lo_4372_, lean_object* v_hi_4373_, lean_object* v_hhi_4374_, lean_object* v_pivot_4375_, lean_object* v_as_4376_, lean_object* v_i_4377_, lean_object* v_k_4378_, lean_object* v_ilo_4379_, lean_object* v_ik_4380_, lean_object* v_w_4381_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_4373_, v_pivot_4375_, v_as_4376_, v_i_4377_, v_k_4378_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_4383_, lean_object* v_lo_4384_, lean_object* v_hi_4385_, lean_object* v_hhi_4386_, lean_object* v_pivot_4387_, lean_object* v_as_4388_, lean_object* v_i_4389_, lean_object* v_k_4390_, lean_object* v_ilo_4391_, lean_object* v_ik_4392_, lean_object* v_w_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_4383_, v_lo_4384_, v_hi_4385_, v_hhi_4386_, v_pivot_4387_, v_as_4388_, v_i_4389_, v_k_4390_, v_ilo_4391_, v_ik_4392_, v_w_4393_);
lean_dec(v_hi_4385_);
lean_dec(v_lo_4384_);
lean_dec(v_n_4383_);
return v_res_4394_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_4395_, size_t v_sz_4396_, size_t v_i_4397_, lean_object* v_b_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4395_, v_sz_4396_, v_i_4397_, v_b_4398_);
return v___x_4402_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4395_ = stack[0].m_obj;
size_t v_sz_4396_ = stack[1].m_num;
size_t v_i_4397_ = stack[2].m_num;
lean_object* v_b_4398_ = stack[3].m_obj;
lean_object* v___y_4399_ = stack[4].m_obj;
lean_object* v___y_4400_ = stack[5].m_obj;
lean_object* v_res_4403_;
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4395_, v_sz_4396_, v_i_4397_, v_b_4398_, v___y_4399_, v___y_4400_);
stack->m_obj
 = v_res_4403_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_4404_, lean_object* v_sz_4405_, lean_object* v_i_4406_, lean_object* v_b_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
size_t v_sz_boxed_4411_; size_t v_i_boxed_4412_; lean_object* v_res_4413_; 
v_sz_boxed_4411_ = lean_unbox_usize(v_sz_4405_);
lean_dec(v_sz_4405_);
v_i_boxed_4412_ = lean_unbox_usize(v_i_4406_);
lean_dec(v_i_4406_);
v_res_4413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4404_, v_sz_boxed_4411_, v_i_boxed_4412_, v_b_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec_ref(v_as_4404_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_4414_, lean_object* v_t_4415_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4414_, v_t_4415_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_4417_, lean_object* v_t_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_4417_, v_t_4418_);
lean_dec(v_t_4418_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_4420_, lean_object* v_as_4421_, lean_object* v_lo_4422_, lean_object* v_hi_4423_, lean_object* v_w_4424_, lean_object* v_hlo_4425_, lean_object* v_hhi_4426_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4420_, v_as_4421_, v_lo_4422_, v_hi_4423_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_4428_, lean_object* v_as_4429_, lean_object* v_lo_4430_, lean_object* v_hi_4431_, lean_object* v_w_4432_, lean_object* v_hlo_4433_, lean_object* v_hhi_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_4428_, v_as_4429_, v_lo_4430_, v_hi_4431_, v_w_4432_, v_hlo_4433_, v_hhi_4434_);
lean_dec(v_hi_4431_);
lean_dec(v_n_4428_);
return v_res_4435_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_4436_, lean_object* v_x_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4436_, v_x_4437_);
return v___x_4441_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4436_ = stack[0].m_obj;
lean_object* v_x_4437_ = stack[1].m_obj;
lean_object* v___y_4438_ = stack[2].m_obj;
lean_object* v___y_4439_ = stack[3].m_obj;
lean_object* v_res_4442_;
v_res_4442_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4436_, v_x_4437_, v___y_4438_, v___y_4439_);
stack->m_obj
 = v_res_4442_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_4443_, lean_object* v_x_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4443_, v_x_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
return v_res_4448_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_4449_, lean_object* v_x_4450_, size_t v_x_4451_, lean_object* v_x_4452_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_4450_, v_x_4451_, v_x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4450_ = stack[1].m_obj;
size_t v_x_4451_ = stack[2].m_num;
lean_object* v_x_4452_ = stack[3].m_obj;
lean_object* v_res_4454_;
v_res_4454_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_box(0), v_x_4450_, v_x_4451_, v_x_4452_);
stack->m_obj
 = v_res_4454_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4455_, lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v_x_4458_){
_start:
{
size_t v_x_20032__boxed_4459_; lean_object* v_res_4460_; 
v_x_20032__boxed_4459_ = lean_unbox_usize(v_x_4457_);
lean_dec(v_x_4457_);
v_res_4460_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_4455_, v_x_4456_, v_x_20032__boxed_4459_, v_x_4458_);
lean_dec(v_x_4458_);
lean_dec_ref(v_x_4456_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_4461_, lean_object* v_k_4462_, lean_object* v_x_4463_, lean_object* v_x_4464_, lean_object* v_x_4465_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_4461_, v_k_4462_, v_x_4463_, v_x_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_4467_, lean_object* v_k_4468_, lean_object* v_x_4469_, lean_object* v_x_4470_, lean_object* v_x_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_4467_, v_k_4468_, v_x_4469_, v_x_4470_, v_x_4471_);
lean_dec_ref(v_k_4468_);
lean_dec_ref(v_as_4467_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_4473_, lean_object* v_m_4474_, lean_object* v_a_4475_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_4474_, v_a_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_4477_, lean_object* v_m_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_4477_, v_m_4478_, v_a_4479_);
lean_dec(v_a_4479_);
lean_dec_ref(v_m_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_4481_, lean_object* v_lo_4482_, lean_object* v_hi_4483_, lean_object* v_hhi_4484_, lean_object* v_pivot_4485_, lean_object* v_as_4486_, lean_object* v_i_4487_, lean_object* v_k_4488_, lean_object* v_ilo_4489_, lean_object* v_ik_4490_, lean_object* v_w_4491_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4483_, v_pivot_4485_, v_as_4486_, v_i_4487_, v_k_4488_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_4493_, lean_object* v_lo_4494_, lean_object* v_hi_4495_, lean_object* v_hhi_4496_, lean_object* v_pivot_4497_, lean_object* v_as_4498_, lean_object* v_i_4499_, lean_object* v_k_4500_, lean_object* v_ilo_4501_, lean_object* v_ik_4502_, lean_object* v_w_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_4493_, v_lo_4494_, v_hi_4495_, v_hhi_4496_, v_pivot_4497_, v_as_4498_, v_i_4499_, v_k_4500_, v_ilo_4501_, v_ik_4502_, v_w_4503_);
lean_dec(v_hi_4495_);
lean_dec(v_lo_4494_);
lean_dec(v_n_4493_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_4505_, lean_object* v_keys_4506_, lean_object* v_vals_4507_, lean_object* v_heq_4508_, lean_object* v_i_4509_, lean_object* v_k_4510_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_4506_, v_vals_4507_, v_i_4509_, v_k_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_4512_, lean_object* v_keys_4513_, lean_object* v_vals_4514_, lean_object* v_heq_4515_, lean_object* v_i_4516_, lean_object* v_k_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_4512_, v_keys_4513_, v_vals_4514_, v_heq_4515_, v_i_4516_, v_k_4517_);
lean_dec(v_k_4517_);
lean_dec_ref(v_vals_4514_);
lean_dec_ref(v_keys_4513_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_4519_, lean_object* v_a_4520_, lean_object* v_x_4521_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_4520_, v_x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_4523_, lean_object* v_a_4524_, lean_object* v_x_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_4523_, v_a_4524_, v_x_4525_);
lean_dec(v_x_4525_);
lean_dec(v_a_4524_);
return v_res_4526_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4541_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_4543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4544_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_4545_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4541_, v___x_4542_, v___x_4543_, v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4546_;
v_res_4546_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
stack->m_obj
 = v_res_4546_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_4548_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_4553_ = l_Lean_addBuiltinDocString(v___x_4551_, v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4554_;
v_res_4554_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
stack->m_obj
 = v_res_4554_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_4556_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_4585_ = l_Lean_addBuiltinDeclarationRanges(v___x_4583_, v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4586_;
v_res_4586_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
stack->m_obj
 = v_res_4586_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_4588_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_4589_, lean_object* v___x_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, uint8_t v_includeUnnamed_4593_, lean_object* v_x_4594_, lean_object* v_____s_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v_fst_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4656_; 
v_fst_4601_ = lean_ctor_get(v_x_4594_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v_x_4594_);
if (v_isSharedCheck_4656_ == 0)
{
lean_object* v_unused_4657_; 
v_unused_4657_ = lean_ctor_get(v_x_4594_, 1);
lean_dec(v_unused_4657_);
v___x_4603_ = v_x_4594_;
v_isShared_4604_ = v_isSharedCheck_4656_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_fst_4601_);
lean_dec(v_x_4594_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4656_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v_userName_4606_; lean_object* v___y_4607_; lean_object* v___x_4641_; 
lean_inc(v_fst_4601_);
lean_inc_ref(v_env_4589_);
v___x_4641_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4589_, v_fst_4601_);
if (lean_obj_tag(v___x_4641_) == 1)
{
lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4649_; 
lean_del_object(v___x_4603_);
lean_dec(v_fst_4601_);
lean_dec(v___x_4590_);
lean_dec_ref(v_env_4589_);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v___x_4641_, 0);
lean_dec(v_unused_4650_);
v___x_4643_ = v___x_4641_;
v_isShared_4644_ = v_isSharedCheck_4649_;
goto v_resetjp_4642_;
}
else
{
lean_dec(v___x_4641_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4649_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 0, v_____s_4595_);
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_____s_4595_);
v___x_4646_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
lean_object* v___x_4647_; 
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
return v___x_4647_;
}
}
}
else
{
lean_object* v___x_4651_; 
lean_dec(v___x_4641_);
v___x_4651_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_4592_, v_fst_4601_);
if (lean_obj_tag(v___x_4651_) == 1)
{
lean_object* v_val_4652_; 
v_val_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_val_4652_);
lean_dec_ref_known(v___x_4651_, 1);
v_userName_4606_ = v_val_4652_;
v___y_4607_ = v___y_4598_;
goto v___jp_4605_;
}
else
{
lean_dec(v___x_4651_);
if (v_includeUnnamed_4593_ == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
lean_del_object(v___x_4603_);
lean_dec(v_fst_4601_);
lean_dec(v___x_4590_);
lean_dec_ref(v_env_4589_);
v___x_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_____s_4595_);
v___x_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
return v___x_4654_;
}
else
{
lean_object* v___x_4655_; 
lean_inc(v_fst_4601_);
v___x_4655_ = l_Lean_Name_toString(v_fst_4601_, v_includeUnnamed_4593_);
v_userName_4606_ = v___x_4655_;
v___y_4607_ = v___y_4598_;
goto v___jp_4605_;
}
}
}
v___jp_4605_:
{
lean_object* v_ref_4608_; uint8_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v_ref_4608_ = lean_ctor_get(v___y_4607_, 2);
v___x_4609_ = 1;
v___x_4610_ = l_Lean_Options_empty;
v___x_4611_ = lean_box(0);
lean_inc(v_fst_4601_);
lean_inc_ref(v_env_4589_);
v___x_4612_ = l_Lean_findDocString_x3f(v_env_4589_, v_fst_4601_, v___x_4609_, v___x_4610_, v___x_4590_, v___x_4611_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4626_; 
lean_del_object(v___x_4603_);
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4626_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4626_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4624_; 
v___x_4617_ = l_Lean_NameSet_empty;
v___x_4618_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_4591_, v_fst_4601_, v___x_4617_);
lean_inc(v_fst_4601_);
v___x_4619_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_4589_, v_fst_4601_);
v___x_4620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4620_, 0, v_fst_4601_);
lean_ctor_set(v___x_4620_, 1, v_userName_4606_);
lean_ctor_set(v___x_4620_, 2, v___x_4618_);
lean_ctor_set(v___x_4620_, 3, v_a_4613_);
lean_ctor_set(v___x_4620_, 4, v___x_4619_);
v___x_4621_ = lean_array_push(v_____s_4595_, v___x_4620_);
v___x_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4622_);
v___x_4624_ = v___x_4615_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4640_; 
lean_dec_ref(v_userName_4606_);
lean_dec(v_fst_4601_);
lean_dec_ref(v_____s_4595_);
lean_dec_ref(v_env_4589_);
v_a_4627_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4629_ = v___x_4612_;
v_isShared_4630_ = v_isSharedCheck_4640_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4612_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4640_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4631_ = lean_io_error_to_string(v_a_4627_);
v___x_4632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
v___x_4633_ = l_Lean_MessageData_ofFormat(v___x_4632_);
lean_inc(v_ref_4608_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 1, v___x_4633_);
lean_ctor_set(v___x_4603_, 0, v_ref_4608_);
v___x_4635_ = v___x_4603_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_ref_4608_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4637_; 
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4635_);
v___x_4637_ = v___x_4629_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4589_ = stack[0].m_obj;
lean_object* v___x_4590_ = stack[1].m_obj;
lean_object* v_a_4591_ = stack[2].m_obj;
lean_object* v_a_4592_ = stack[3].m_obj;
uint8_t v_includeUnnamed_4593_ = stack[4].m_num;
lean_object* v_x_4594_ = stack[5].m_obj;
lean_object* v_____s_4595_ = stack[6].m_obj;
lean_object* v___y_4596_ = stack[7].m_obj;
lean_object* v___y_4597_ = stack[8].m_obj;
lean_object* v___y_4598_ = stack[9].m_obj;
lean_object* v___y_4599_ = stack[10].m_obj;
lean_object* v_res_4658_;
v_res_4658_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4589_, v___x_4590_, v_a_4591_, v_a_4592_, v_includeUnnamed_4593_, v_x_4594_, v_____s_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
stack->m_obj
 = v_res_4658_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_4659_, lean_object* v___x_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_includeUnnamed_4663_, lean_object* v_x_4664_, lean_object* v_____s_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
uint8_t v_includeUnnamed_boxed_4671_; lean_object* v_res_4672_; 
v_includeUnnamed_boxed_4671_ = lean_unbox(v_includeUnnamed_4663_);
v_res_4672_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4659_, v___x_4660_, v_a_4661_, v_a_4662_, v_includeUnnamed_boxed_4671_, v_x_4664_, v_____s_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_a_4662_);
lean_dec(v_a_4661_);
return v_res_4672_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_4673_, size_t v_sz_4674_, size_t v_i_4675_, lean_object* v_b_4676_){
_start:
{
uint8_t v___x_4678_; 
v___x_4678_ = lean_usize_dec_lt(v_i_4675_, v_sz_4674_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v_b_4676_);
return v___x_4679_;
}
else
{
lean_object* v_a_4680_; lean_object* v_fst_4681_; lean_object* v_snd_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; size_t v___x_4687_; size_t v___x_4688_; 
v_a_4680_ = lean_array_uget_borrowed(v_as_4673_, v_i_4675_);
v_fst_4681_ = lean_ctor_get(v_a_4680_, 0);
v_snd_4682_ = lean_ctor_get(v_a_4680_, 1);
v___x_4683_ = l_Lean_NameSet_empty;
v___x_4684_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4676_, v_fst_4681_, v___x_4683_);
lean_inc(v_snd_4682_);
v___x_4685_ = l_Lean_NameSet_insert(v___x_4684_, v_snd_4682_);
lean_inc(v_fst_4681_);
v___x_4686_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4681_, v___x_4685_, v_b_4676_);
v___x_4687_ = ((size_t)1ULL);
v___x_4688_ = lean_usize_add(v_i_4675_, v___x_4687_);
v_i_4675_ = v___x_4688_;
v_b_4676_ = v___x_4686_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4673_ = stack[0].m_obj;
size_t v_sz_4674_ = stack[1].m_num;
size_t v_i_4675_ = stack[2].m_num;
lean_object* v_b_4676_ = stack[3].m_obj;
lean_object* v_res_4690_;
v_res_4690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4673_, v_sz_4674_, v_i_4675_, v_b_4676_);
stack->m_obj
 = v_res_4690_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_4691_, lean_object* v_sz_4692_, lean_object* v_i_4693_, lean_object* v_b_4694_, lean_object* v___y_4695_){
_start:
{
size_t v_sz_boxed_4696_; size_t v_i_boxed_4697_; lean_object* v_res_4698_; 
v_sz_boxed_4696_ = lean_unbox_usize(v_sz_4692_);
lean_dec(v_sz_4692_);
v_i_boxed_4697_ = lean_unbox_usize(v_i_4693_);
lean_dec(v_i_4693_);
v_res_4698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4691_, v_sz_boxed_4696_, v_i_boxed_4697_, v_b_4694_);
lean_dec_ref(v_as_4691_);
return v_res_4698_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_4699_, size_t v_sz_4700_, size_t v_i_4701_, lean_object* v_b_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
uint8_t v___x_4708_; 
v___x_4708_ = lean_usize_dec_lt(v_i_4701_, v_sz_4700_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v_b_4702_);
return v___x_4709_;
}
else
{
lean_object* v_a_4710_; size_t v_sz_4711_; size_t v___x_4712_; lean_object* v___x_4713_; 
v_a_4710_ = lean_array_uget_borrowed(v_as_4699_, v_i_4701_);
v_sz_4711_ = lean_array_size(v_a_4710_);
v___x_4712_ = ((size_t)0ULL);
v___x_4713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_4710_, v_sz_4711_, v___x_4712_, v_b_4702_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; size_t v___x_4715_; size_t v___x_4716_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
lean_inc(v_a_4714_);
lean_dec_ref_known(v___x_4713_, 1);
v___x_4715_ = ((size_t)1ULL);
v___x_4716_ = lean_usize_add(v_i_4701_, v___x_4715_);
v_i_4701_ = v___x_4716_;
v_b_4702_ = v_a_4714_;
goto _start;
}
else
{
return v___x_4713_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4699_ = stack[0].m_obj;
size_t v_sz_4700_ = stack[1].m_num;
size_t v_i_4701_ = stack[2].m_num;
lean_object* v_b_4702_ = stack[3].m_obj;
lean_object* v___y_4703_ = stack[4].m_obj;
lean_object* v___y_4704_ = stack[5].m_obj;
lean_object* v___y_4705_ = stack[6].m_obj;
lean_object* v___y_4706_ = stack[7].m_obj;
lean_object* v_res_4718_;
v_res_4718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4699_, v_sz_4700_, v_i_4701_, v_b_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
stack->m_obj
 = v_res_4718_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_4719_, lean_object* v_sz_4720_, lean_object* v_i_4721_, lean_object* v_b_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
size_t v_sz_boxed_4728_; size_t v_i_boxed_4729_; lean_object* v_res_4730_; 
v_sz_boxed_4728_ = lean_unbox_usize(v_sz_4720_);
lean_dec(v_sz_4720_);
v_i_boxed_4729_ = lean_unbox_usize(v_i_4721_);
lean_dec(v_i_4721_);
v_res_4730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4719_, v_sz_boxed_4728_, v_i_boxed_4729_, v_b_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec_ref(v_as_4719_);
return v_res_4730_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_4731_, lean_object* v_keys_4732_, lean_object* v_vals_4733_, lean_object* v_i_4734_, lean_object* v_acc_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4741_ = lean_array_get_size(v_keys_4732_);
v___x_4742_ = lean_nat_dec_lt(v_i_4734_, v___x_4741_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
lean_dec(v_i_4734_);
lean_dec_ref(v_f_4731_);
v___x_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4743_, 0, v_acc_4735_);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
else
{
lean_object* v_k_4745_; lean_object* v_v_4746_; lean_object* v___x_4747_; 
v_k_4745_ = lean_array_fget_borrowed(v_keys_4732_, v_i_4734_);
v_v_4746_ = lean_array_fget_borrowed(v_vals_4733_, v_i_4734_);
lean_inc_ref(v_f_4731_);
lean_inc(v___y_4739_);
lean_inc_ref(v___y_4738_);
lean_inc(v___y_4737_);
lean_inc_ref(v___y_4736_);
lean_inc(v_v_4746_);
lean_inc(v_k_4745_);
v___x_4747_ = lean_apply_8(v_f_4731_, v_acc_4735_, v_k_4745_, v_v_4746_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, lean_box(0));
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
if (lean_obj_tag(v_a_4748_) == 0)
{
lean_dec_ref_known(v_a_4748_, 1);
lean_dec(v_i_4734_);
lean_dec_ref(v_f_4731_);
return v___x_4747_;
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
lean_dec_ref_known(v___x_4747_, 1);
v_a_4749_ = lean_ctor_get(v_a_4748_, 0);
lean_inc(v_a_4749_);
lean_dec_ref_known(v_a_4748_, 1);
v___x_4750_ = lean_unsigned_to_nat(1u);
v___x_4751_ = lean_nat_add(v_i_4734_, v___x_4750_);
lean_dec(v_i_4734_);
v_i_4734_ = v___x_4751_;
v_acc_4735_ = v_a_4749_;
goto _start;
}
}
else
{
lean_dec(v_i_4734_);
lean_dec_ref(v_f_4731_);
return v___x_4747_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4731_ = stack[0].m_obj;
lean_object* v_keys_4732_ = stack[1].m_obj;
lean_object* v_vals_4733_ = stack[2].m_obj;
lean_object* v_i_4734_ = stack[3].m_obj;
lean_object* v_acc_4735_ = stack[4].m_obj;
lean_object* v___y_4736_ = stack[5].m_obj;
lean_object* v___y_4737_ = stack[6].m_obj;
lean_object* v___y_4738_ = stack[7].m_obj;
lean_object* v___y_4739_ = stack[8].m_obj;
lean_object* v_res_4753_;
v_res_4753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4731_, v_keys_4732_, v_vals_4733_, v_i_4734_, v_acc_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
stack->m_obj
 = v_res_4753_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_4754_, lean_object* v_keys_4755_, lean_object* v_vals_4756_, lean_object* v_i_4757_, lean_object* v_acc_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4754_, v_keys_4755_, v_vals_4756_, v_i_4757_, v_acc_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec_ref(v_vals_4756_);
lean_dec_ref(v_keys_4755_);
return v_res_4764_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_4765_, lean_object* v_as_4766_, size_t v_i_4767_, size_t v_stop_4768_, lean_object* v_b_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v_a_4776_; lean_object* v___y_4781_; uint8_t v___x_4784_; 
v___x_4784_ = lean_usize_dec_eq(v_i_4767_, v_stop_4768_);
if (v___x_4784_ == 0)
{
lean_object* v___x_4785_; 
v___x_4785_ = lean_array_uget_borrowed(v_as_4766_, v_i_4767_);
switch(lean_obj_tag(v___x_4785_))
{
case 0:
{
lean_object* v_key_4786_; lean_object* v_val_4787_; lean_object* v___x_4788_; 
v_key_4786_ = lean_ctor_get(v___x_4785_, 0);
v_val_4787_ = lean_ctor_get(v___x_4785_, 1);
lean_inc_ref(v_f_4765_);
lean_inc(v___y_4773_);
lean_inc_ref(v___y_4772_);
lean_inc(v___y_4771_);
lean_inc_ref(v___y_4770_);
lean_inc(v_val_4787_);
lean_inc(v_key_4786_);
v___x_4788_ = lean_apply_8(v_f_4765_, v_b_4769_, v_key_4786_, v_val_4787_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, lean_box(0));
v___y_4781_ = v___x_4788_;
goto v___jp_4780_;
}
case 1:
{
lean_object* v_node_4789_; lean_object* v___x_4790_; 
v_node_4789_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_node_4789_);
lean_inc_ref(v_f_4765_);
v___x_4790_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4765_, v_node_4789_, v_b_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
v___y_4781_ = v___x_4790_;
goto v___jp_4780_;
}
default: 
{
v_a_4776_ = v_b_4769_;
goto v___jp_4775_;
}
}
}
else
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
lean_dec_ref(v_f_4765_);
v___x_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_b_4769_);
v___x_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
return v___x_4792_;
}
v___jp_4775_:
{
size_t v___x_4777_; size_t v___x_4778_; 
v___x_4777_ = ((size_t)1ULL);
v___x_4778_ = lean_usize_add(v_i_4767_, v___x_4777_);
v_i_4767_ = v___x_4778_;
v_b_4769_ = v_a_4776_;
goto _start;
}
v___jp_4780_:
{
if (lean_obj_tag(v___y_4781_) == 0)
{
lean_object* v_a_4782_; 
v_a_4782_ = lean_ctor_get(v___y_4781_, 0);
if (lean_obj_tag(v_a_4782_) == 0)
{
lean_dec_ref(v_f_4765_);
return v___y_4781_;
}
else
{
lean_object* v_a_4783_; 
lean_inc_ref(v_a_4782_);
lean_dec_ref_known(v___y_4781_, 1);
v_a_4783_ = lean_ctor_get(v_a_4782_, 0);
lean_inc(v_a_4783_);
lean_dec_ref_known(v_a_4782_, 1);
v_a_4776_ = v_a_4783_;
goto v___jp_4775_;
}
}
else
{
lean_dec_ref(v_f_4765_);
return v___y_4781_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4765_ = stack[0].m_obj;
lean_object* v_as_4766_ = stack[1].m_obj;
size_t v_i_4767_ = stack[2].m_num;
size_t v_stop_4768_ = stack[3].m_num;
lean_object* v_b_4769_ = stack[4].m_obj;
lean_object* v___y_4770_ = stack[5].m_obj;
lean_object* v___y_4771_ = stack[6].m_obj;
lean_object* v___y_4772_ = stack[7].m_obj;
lean_object* v___y_4773_ = stack[8].m_obj;
lean_object* v_res_4793_;
v_res_4793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4765_, v_as_4766_, v_i_4767_, v_stop_4768_, v_b_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
stack->m_obj
 = v_res_4793_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_4794_, lean_object* v_x_4795_, lean_object* v_x_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
if (lean_obj_tag(v_x_4795_) == 0)
{
lean_object* v_es_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4816_; 
v_es_4802_ = lean_ctor_get(v_x_4795_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v_x_4795_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4804_ = v_x_4795_;
v_isShared_4805_ = v_isSharedCheck_4816_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_es_4802_);
lean_dec(v_x_4795_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4816_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4806_ = lean_unsigned_to_nat(0u);
v___x_4807_ = lean_array_get_size(v_es_4802_);
v___x_4808_ = lean_nat_dec_lt(v___x_4806_, v___x_4807_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4810_; 
lean_dec_ref(v_es_4802_);
lean_dec_ref(v_f_4794_);
if (v_isShared_4805_ == 0)
{
lean_ctor_set_tag(v___x_4804_, 1);
lean_ctor_set(v___x_4804_, 0, v_x_4796_);
v___x_4810_ = v___x_4804_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_x_4796_);
v___x_4810_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
return v___x_4811_;
}
}
else
{
size_t v___x_4813_; size_t v___x_4814_; lean_object* v___x_4815_; 
lean_del_object(v___x_4804_);
v___x_4813_ = ((size_t)0ULL);
v___x_4814_ = lean_usize_of_nat(v___x_4807_);
v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4794_, v_es_4802_, v___x_4813_, v___x_4814_, v_x_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
lean_dec_ref(v_es_4802_);
return v___x_4815_;
}
}
}
else
{
lean_object* v_ks_4817_; lean_object* v_vs_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v_ks_4817_ = lean_ctor_get(v_x_4795_, 0);
lean_inc_ref(v_ks_4817_);
v_vs_4818_ = lean_ctor_get(v_x_4795_, 1);
lean_inc_ref(v_vs_4818_);
lean_dec_ref_known(v_x_4795_, 2);
v___x_4819_ = lean_unsigned_to_nat(0u);
v___x_4820_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4794_, v_ks_4817_, v_vs_4818_, v___x_4819_, v_x_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
lean_dec_ref(v_vs_4818_);
lean_dec_ref(v_ks_4817_);
return v___x_4820_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4794_ = stack[0].m_obj;
lean_object* v_x_4795_ = stack[1].m_obj;
lean_object* v_x_4796_ = stack[2].m_obj;
lean_object* v___y_4797_ = stack[3].m_obj;
lean_object* v___y_4798_ = stack[4].m_obj;
lean_object* v___y_4799_ = stack[5].m_obj;
lean_object* v___y_4800_ = stack[6].m_obj;
lean_object* v_res_4821_;
v_res_4821_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4794_, v_x_4795_, v_x_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
stack->m_obj
 = v_res_4821_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_4822_, lean_object* v_x_4823_, lean_object* v_x_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4822_, v_x_4823_, v_x_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_4831_, lean_object* v_as_4832_, lean_object* v_i_4833_, lean_object* v_stop_4834_, lean_object* v_b_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
size_t v_i_boxed_4841_; size_t v_stop_boxed_4842_; lean_object* v_res_4843_; 
v_i_boxed_4841_ = lean_unbox_usize(v_i_4833_);
lean_dec(v_i_4833_);
v_stop_boxed_4842_ = lean_unbox_usize(v_stop_4834_);
lean_dec(v_stop_4834_);
v_res_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4831_, v_as_4832_, v_i_boxed_4841_, v_stop_boxed_4842_, v_b_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec_ref(v_as_4832_);
return v_res_4843_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_4844_, lean_object* v_s_4845_, lean_object* v_a_4846_, lean_object* v_b_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4853_, 0, v_a_4846_);
lean_ctor_set(v___x_4853_, 1, v_b_4847_);
lean_inc(v___y_4851_);
lean_inc_ref(v___y_4850_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
v___x_4854_ = lean_apply_7(v_f_4844_, v___x_4853_, v_s_4845_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, lean_box(0));
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4881_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4857_ = v___x_4854_;
v_isShared_4858_ = v_isSharedCheck_4881_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4854_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4881_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
if (lean_obj_tag(v_a_4855_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4869_; 
v_a_4859_ = lean_ctor_get(v_a_4855_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v_a_4855_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4861_ = v_a_4855_;
v_isShared_4862_ = v_isSharedCheck_4869_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v_a_4855_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4869_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
lean_object* v___x_4866_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4864_);
v___x_4866_ = v___x_4857_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
else
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4880_; 
v_a_4870_ = lean_ctor_get(v_a_4855_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v_a_4855_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4872_ = v_a_4855_;
v_isShared_4873_ = v_isSharedCheck_4880_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v_a_4855_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4880_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
lean_object* v___x_4877_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4875_);
v___x_4877_ = v___x_4857_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_a_4882_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4854_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4854_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4844_ = stack[0].m_obj;
lean_object* v_s_4845_ = stack[1].m_obj;
lean_object* v_a_4846_ = stack[2].m_obj;
lean_object* v_b_4847_ = stack[3].m_obj;
lean_object* v___y_4848_ = stack[4].m_obj;
lean_object* v___y_4849_ = stack[5].m_obj;
lean_object* v___y_4850_ = stack[6].m_obj;
lean_object* v___y_4851_ = stack[7].m_obj;
lean_object* v_res_4890_;
v_res_4890_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_4844_, v_s_4845_, v_a_4846_, v_b_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
stack->m_obj
 = v_res_4890_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_4891_, lean_object* v_s_4892_, lean_object* v_a_4893_, lean_object* v_b_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_4891_, v_s_4892_, v_a_4893_, v_b_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
return v_res_4900_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_4901_, lean_object* v_init_4902_, lean_object* v_f_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___f_4909_; lean_object* v___x_4910_; 
v___f_4909_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4909_, 0, v_f_4903_);
lean_inc_ref(v_map_4901_);
v___x_4910_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_4909_, v_map_4901_, v_init_4902_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4919_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4913_ = v___x_4910_;
v_isShared_4914_ = v_isSharedCheck_4919_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4910_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4919_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v_a_4915_; lean_object* v___x_4917_; 
v_a_4915_ = lean_ctor_get(v_a_4911_, 0);
lean_inc(v_a_4915_);
lean_dec(v_a_4911_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v_a_4915_);
v___x_4917_ = v___x_4913_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4915_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
v_a_4920_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4910_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4910_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4901_ = stack[0].m_obj;
lean_object* v_init_4902_ = stack[1].m_obj;
lean_object* v_f_4903_ = stack[2].m_obj;
lean_object* v___y_4904_ = stack[3].m_obj;
lean_object* v___y_4905_ = stack[4].m_obj;
lean_object* v___y_4906_ = stack[5].m_obj;
lean_object* v___y_4907_ = stack[6].m_obj;
lean_object* v_res_4928_;
v_res_4928_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4901_, v_init_4902_, v_f_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
stack->m_obj
 = v_res_4928_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_4929_, lean_object* v_init_4930_, lean_object* v_f_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4929_, v_init_4930_, v_f_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec_ref(v_map_4929_);
return v_res_4937_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_4938_){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v_env_4944_; lean_object* v___x_4945_; lean_object* v_ext_4946_; lean_object* v_toEnvExtension_4947_; lean_object* v_asyncMode_4948_; uint8_t v___x_4949_; lean_object* v___x_4950_; lean_object* v_categories_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4940_ = lean_box(1);
v___x_4941_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4942_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4943_ = lean_st_ref_get(v___y_4938_);
v_env_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc_ref_n(v_env_4944_, 2);
lean_dec(v___x_4943_);
v___x_4945_ = l_Lean_Parser_parserExtension;
v_ext_4946_ = lean_ctor_get(v___x_4945_, 1);
v_toEnvExtension_4947_ = lean_ctor_get(v_ext_4946_, 0);
v_asyncMode_4948_ = lean_ctor_get(v_toEnvExtension_4947_, 2);
v___x_4949_ = 0;
v___x_4950_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4942_, v___x_4945_, v_env_4944_, v_asyncMode_4948_, v___x_4949_);
v_categories_4951_ = lean_ctor_get(v___x_4950_, 2);
lean_inc_ref(v_categories_4951_);
lean_dec(v___x_4950_);
v___x_4952_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4953_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4951_, v___x_4952_);
lean_dec_ref(v_categories_4951_);
if (lean_obj_tag(v___x_4953_) == 1)
{
lean_object* v_val_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4985_; 
v_val_4954_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4956_ = v___x_4953_;
v_isShared_4957_ = v_isSharedCheck_4985_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_val_4954_);
lean_dec(v___x_4953_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4985_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___y_4959_; lean_object* v___x_4968_; lean_object* v_toEnvExtension_4969_; lean_object* v_exportEntriesFn_4970_; lean_object* v_asyncMode_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v_importedEntries_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v_exported_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; uint8_t v___x_4981_; 
v___x_4968_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4969_ = lean_ctor_get(v___x_4968_, 0);
v_exportEntriesFn_4970_ = lean_ctor_get(v___x_4968_, 4);
v_asyncMode_4971_ = lean_ctor_get(v_toEnvExtension_4969_, 2);
v___x_4972_ = lean_box(0);
lean_inc_ref_n(v_env_4944_, 2);
v___x_4973_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4941_, v_toEnvExtension_4969_, v_env_4944_, v_asyncMode_4971_, v___x_4972_, v___x_4949_);
v_importedEntries_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc_ref(v_importedEntries_4974_);
lean_dec(v___x_4973_);
v___x_4975_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4940_, v___x_4968_, v_env_4944_, v_asyncMode_4971_, v___x_4972_, v___x_4949_);
lean_inc_ref(v_exportEntriesFn_4970_);
v___x_4976_ = lean_apply_2(v_exportEntriesFn_4970_, v_env_4944_, v___x_4975_);
v_exported_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_exported_4977_);
lean_dec_ref(v___x_4976_);
v___x_4978_ = lean_array_push(v_importedEntries_4974_, v_exported_4977_);
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = lean_array_get_size(v___x_4978_);
v___x_4981_ = lean_nat_dec_lt(v___x_4979_, v___x_4980_);
if (v___x_4981_ == 0)
{
lean_dec_ref(v___x_4978_);
v___y_4959_ = v___x_4940_;
goto v___jp_4958_;
}
else
{
size_t v___x_4982_; size_t v___x_4983_; lean_object* v___x_4984_; 
v___x_4982_ = ((size_t)0ULL);
v___x_4983_ = lean_usize_of_nat(v___x_4980_);
v___x_4984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4978_, v___x_4982_, v___x_4983_, v___x_4940_);
lean_dec_ref(v___x_4978_);
v___y_4959_ = v___x_4984_;
goto v___jp_4958_;
}
v___jp_4958_:
{
lean_object* v_tables_4960_; lean_object* v_leadingTable_4961_; lean_object* v_trailingTable_4962_; lean_object* v_firstTokens_4963_; lean_object* v_firstTokens_4964_; lean_object* v___x_4966_; 
v_tables_4960_ = lean_ctor_get(v_val_4954_, 2);
v_leadingTable_4961_ = lean_ctor_get(v_tables_4960_, 0);
v_trailingTable_4962_ = lean_ctor_get(v_tables_4960_, 2);
lean_inc(v_trailingTable_4962_);
lean_inc(v_leadingTable_4961_);
lean_inc(v_val_4954_);
v_firstTokens_4963_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4954_, v_leadingTable_4961_, v___y_4959_);
v_firstTokens_4964_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4954_, v_trailingTable_4962_, v_firstTokens_4963_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set_tag(v___x_4956_, 0);
lean_ctor_set(v___x_4956_, 0, v_firstTokens_4964_);
v___x_4966_ = v___x_4956_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_firstTokens_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
else
{
lean_object* v___x_4986_; 
lean_dec(v___x_4953_);
lean_dec_ref(v_env_4944_);
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4940_);
return v___x_4986_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4938_ = stack[0].m_obj;
lean_object* v_res_4987_;
v_res_4987_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4938_);
stack->m_obj
 = v_res_4987_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4988_);
lean_dec(v___y_4988_);
return v_res_4990_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v_env_5003_; lean_object* v___x_5004_; lean_object* v_toEnvExtension_5005_; lean_object* v_exportEntriesFn_5006_; lean_object* v_asyncMode_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; lean_object* v___x_5010_; lean_object* v_importedEntries_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v_exported_5014_; lean_object* v___x_5015_; size_t v_sz_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
v___x_4999_ = lean_box(1);
v___x_5000_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_5001_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_5002_ = lean_st_ref_get(v_a_4997_);
v_env_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc_ref_n(v_env_5003_, 4);
lean_dec(v___x_5002_);
v___x_5004_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_5005_ = lean_ctor_get(v___x_5004_, 0);
v_exportEntriesFn_5006_ = lean_ctor_get(v___x_5004_, 4);
v_asyncMode_5007_ = lean_ctor_get(v_toEnvExtension_5005_, 2);
v___x_5008_ = lean_box(0);
v___x_5009_ = 0;
v___x_5010_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5000_, v_toEnvExtension_5005_, v_env_5003_, v_asyncMode_5007_, v___x_5008_, v___x_5009_);
v_importedEntries_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc_ref(v_importedEntries_5011_);
lean_dec(v___x_5010_);
v___x_5012_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4999_, v___x_5004_, v_env_5003_, v_asyncMode_5007_, v___x_5008_, v___x_5009_);
lean_inc_ref(v_exportEntriesFn_5006_);
v___x_5013_ = lean_apply_2(v_exportEntriesFn_5006_, v_env_5003_, v___x_5012_);
v_exported_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_exported_5014_);
lean_dec_ref(v___x_5013_);
v___x_5015_ = lean_array_push(v_importedEntries_5011_, v_exported_5014_);
v_sz_5016_ = lean_array_size(v___x_5015_);
v___x_5017_ = ((size_t)0ULL);
v___x_5018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_5015_, v_sz_5016_, v___x_5017_, v___x_4999_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec_ref(v___x_5015_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5042_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5042_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5042_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; lean_object* v_ext_5024_; lean_object* v_toEnvExtension_5025_; lean_object* v_asyncMode_5026_; lean_object* v___x_5027_; lean_object* v_categories_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5023_ = l_Lean_Parser_parserExtension;
v_ext_5024_ = lean_ctor_get(v___x_5023_, 1);
v_toEnvExtension_5025_ = lean_ctor_get(v_ext_5024_, 0);
v_asyncMode_5026_ = lean_ctor_get(v_toEnvExtension_5025_, 2);
lean_inc_ref(v_env_5003_);
v___x_5027_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5001_, v___x_5023_, v_env_5003_, v_asyncMode_5026_, v___x_5009_);
v_categories_5028_ = lean_ctor_get(v___x_5027_, 2);
lean_inc_ref(v_categories_5028_);
lean_dec(v___x_5027_);
v___x_5029_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_5030_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_5031_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_5028_, v___x_5030_);
lean_dec_ref(v_categories_5028_);
if (lean_obj_tag(v___x_5031_) == 1)
{
lean_object* v_val_5032_; lean_object* v___x_5033_; lean_object* v_a_5034_; lean_object* v_kinds_5035_; lean_object* v___x_5036_; lean_object* v___f_5037_; lean_object* v___x_5038_; 
lean_del_object(v___x_5021_);
v_val_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_val_5032_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5033_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_4997_);
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5033_);
v_kinds_5035_ = lean_ctor_get(v_val_5032_, 1);
lean_inc_ref(v_kinds_5035_);
lean_dec(v_val_5032_);
v___x_5036_ = lean_box(v_includeUnnamed_4993_);
v___f_5037_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5037_, 0, v_env_5003_);
lean_closure_set(v___f_5037_, 1, v___x_5008_);
lean_closure_set(v___f_5037_, 2, v_a_5019_);
lean_closure_set(v___f_5037_, 3, v_a_5034_);
lean_closure_set(v___f_5037_, 4, v___x_5036_);
v___x_5038_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_5035_, v___x_5029_, v___f_5037_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec_ref(v_kinds_5035_);
return v___x_5038_;
}
else
{
lean_object* v___x_5040_; 
lean_dec(v___x_5031_);
lean_dec(v_a_5019_);
lean_dec_ref(v_env_5003_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5029_);
v___x_5040_ = v___x_5021_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_5029_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5050_; 
lean_dec_ref(v_env_5003_);
v_a_5043_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5045_ = v___x_5018_;
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5018_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5048_; 
if (v_isShared_5046_ == 0)
{
v___x_5048_ = v___x_5045_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_allTacticDocs_0interp(lean_interpreter_value* stack)
{
uint8_t v_includeUnnamed_4993_ = stack[0].m_num;
lean_object* v_a_4994_ = stack[1].m_obj;
lean_object* v_a_4995_ = stack[2].m_obj;
lean_object* v_a_4996_ = stack[3].m_obj;
lean_object* v_a_4997_ = stack[4].m_obj;
lean_object* v_res_5051_;
v_res_5051_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
stack->m_obj
 = v_res_5051_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_){
_start:
{
uint8_t v_includeUnnamed_boxed_5058_; lean_object* v_res_5059_; 
v_includeUnnamed_boxed_5058_ = lean_unbox(v_includeUnnamed_5052_);
v_res_5059_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_5058_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
return v_res_5059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_5060_, size_t v_sz_5061_, size_t v_i_5062_, lean_object* v_b_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_5060_, v_sz_5061_, v_i_5062_, v_b_5063_);
return v___x_5069_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5060_ = stack[0].m_obj;
size_t v_sz_5061_ = stack[1].m_num;
size_t v_i_5062_ = stack[2].m_num;
lean_object* v_b_5063_ = stack[3].m_obj;
lean_object* v___y_5064_ = stack[4].m_obj;
lean_object* v___y_5065_ = stack[5].m_obj;
lean_object* v___y_5066_ = stack[6].m_obj;
lean_object* v___y_5067_ = stack[7].m_obj;
lean_object* v_res_5070_;
v_res_5070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_5060_, v_sz_5061_, v_i_5062_, v_b_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
stack->m_obj
 = v_res_5070_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_5071_, lean_object* v_sz_5072_, lean_object* v_i_5073_, lean_object* v_b_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
size_t v_sz_boxed_5080_; size_t v_i_boxed_5081_; lean_object* v_res_5082_; 
v_sz_boxed_5080_ = lean_unbox_usize(v_sz_5072_);
lean_dec(v_sz_5072_);
v_i_boxed_5081_ = lean_unbox_usize(v_i_5073_);
lean_dec(v_i_5073_);
v_res_5082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_5071_, v_sz_boxed_5080_, v_i_boxed_5081_, v_b_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec_ref(v_as_5071_);
return v_res_5082_;
}
}
lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_5086_);
return v___x_5088_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5083_ = stack[0].m_obj;
lean_object* v___y_5084_ = stack[1].m_obj;
lean_object* v___y_5085_ = stack[2].m_obj;
lean_object* v___y_5086_ = stack[3].m_obj;
lean_object* v_res_5089_;
v_res_5089_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
stack->m_obj
 = v_res_5089_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
return v_res_5095_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_5096_, lean_object* v_00_u03b2_5097_, lean_object* v_map_5098_, lean_object* v_init_5099_, lean_object* v_f_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_5098_, v_init_5099_, v_f_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
return v___x_5106_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_5098_ = stack[2].m_obj;
lean_object* v_init_5099_ = stack[3].m_obj;
lean_object* v_f_5100_ = stack[4].m_obj;
lean_object* v___y_5101_ = stack[5].m_obj;
lean_object* v___y_5102_ = stack[6].m_obj;
lean_object* v___y_5103_ = stack[7].m_obj;
lean_object* v___y_5104_ = stack[8].m_obj;
lean_object* v_res_5107_;
v_res_5107_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_box(0), lean_box(0), v_map_5098_, v_init_5099_, v_f_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
stack->m_obj
 = v_res_5107_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_5108_, lean_object* v_00_u03b2_5109_, lean_object* v_map_5110_, lean_object* v_init_5111_, lean_object* v_f_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_5108_, v_00_u03b2_5109_, v_map_5110_, v_init_5111_, v_f_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec_ref(v_map_5110_);
return v_res_5118_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_5119_, lean_object* v_f_5120_, lean_object* v_init_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5120_, v_map_5119_, v_init_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
return v___x_5127_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_5119_ = stack[0].m_obj;
lean_object* v_f_5120_ = stack[1].m_obj;
lean_object* v_init_5121_ = stack[2].m_obj;
lean_object* v___y_5122_ = stack[3].m_obj;
lean_object* v___y_5123_ = stack[4].m_obj;
lean_object* v___y_5124_ = stack[5].m_obj;
lean_object* v___y_5125_ = stack[6].m_obj;
lean_object* v_res_5128_;
v_res_5128_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_5119_, v_f_5120_, v_init_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
stack->m_obj
 = v_res_5128_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_5129_, lean_object* v_f_5130_, lean_object* v_init_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_5129_, v_f_5130_, v_init_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec_ref(v___y_5132_);
return v_res_5137_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_5138_, lean_object* v_00_u03c3_5139_, lean_object* v_00_u03b2_5140_, lean_object* v_map_5141_, lean_object* v_f_5142_, lean_object* v_init_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5142_, v_map_5141_, v_init_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
return v___x_5149_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_5141_ = stack[3].m_obj;
lean_object* v_f_5142_ = stack[4].m_obj;
lean_object* v_init_5143_ = stack[5].m_obj;
lean_object* v___y_5144_ = stack[6].m_obj;
lean_object* v___y_5145_ = stack[7].m_obj;
lean_object* v___y_5146_ = stack[8].m_obj;
lean_object* v___y_5147_ = stack[9].m_obj;
lean_object* v_res_5150_;
v_res_5150_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_box(0), lean_box(0), lean_box(0), v_map_5141_, v_f_5142_, v_init_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
stack->m_obj
 = v_res_5150_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_5151_, lean_object* v_00_u03c3_5152_, lean_object* v_00_u03b2_5153_, lean_object* v_map_5154_, lean_object* v_f_5155_, lean_object* v_init_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v_res_5162_; 
v_res_5162_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_5151_, v_00_u03c3_5152_, v_00_u03b2_5153_, v_map_5154_, v_f_5155_, v_init_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
return v_res_5162_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_5163_, lean_object* v_00_u03c3_5164_, lean_object* v_00_u03b1_5165_, lean_object* v_00_u03b2_5166_, lean_object* v_f_5167_, lean_object* v_x_5168_, lean_object* v_x_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v___x_5175_; 
v___x_5175_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5167_, v_x_5168_, v_x_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
return v___x_5175_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5167_ = stack[4].m_obj;
lean_object* v_x_5168_ = stack[5].m_obj;
lean_object* v_x_5169_ = stack[6].m_obj;
lean_object* v___y_5170_ = stack[7].m_obj;
lean_object* v___y_5171_ = stack[8].m_obj;
lean_object* v___y_5172_ = stack[9].m_obj;
lean_object* v___y_5173_ = stack[10].m_obj;
lean_object* v_res_5176_;
v_res_5176_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_5167_, v_x_5168_, v_x_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
stack->m_obj
 = v_res_5176_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_5177_, lean_object* v_00_u03c3_5178_, lean_object* v_00_u03b1_5179_, lean_object* v_00_u03b2_5180_, lean_object* v_f_5181_, lean_object* v_x_5182_, lean_object* v_x_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_5177_, v_00_u03c3_5178_, v_00_u03b1_5179_, v_00_u03b2_5180_, v_f_5181_, v_x_5182_, v_x_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
return v_res_5189_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_5190_, lean_object* v_00_u03b2_5191_, lean_object* v_00_u03c3_5192_, lean_object* v_00_u03c3_5193_, lean_object* v_f_5194_, lean_object* v_as_5195_, size_t v_i_5196_, size_t v_stop_5197_, lean_object* v_b_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5194_, v_as_5195_, v_i_5196_, v_stop_5197_, v_b_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
return v___x_5204_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5194_ = stack[4].m_obj;
lean_object* v_as_5195_ = stack[5].m_obj;
size_t v_i_5196_ = stack[6].m_num;
size_t v_stop_5197_ = stack[7].m_num;
lean_object* v_b_5198_ = stack[8].m_obj;
lean_object* v___y_5199_ = stack[9].m_obj;
lean_object* v___y_5200_ = stack[10].m_obj;
lean_object* v___y_5201_ = stack[11].m_obj;
lean_object* v___y_5202_ = stack[12].m_obj;
lean_object* v_res_5205_;
v_res_5205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_5194_, v_as_5195_, v_i_5196_, v_stop_5197_, v_b_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
stack->m_obj
 = v_res_5205_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5206_, lean_object* v_00_u03b2_5207_, lean_object* v_00_u03c3_5208_, lean_object* v_00_u03c3_5209_, lean_object* v_f_5210_, lean_object* v_as_5211_, lean_object* v_i_5212_, lean_object* v_stop_5213_, lean_object* v_b_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
size_t v_i_boxed_5220_; size_t v_stop_boxed_5221_; lean_object* v_res_5222_; 
v_i_boxed_5220_ = lean_unbox_usize(v_i_5212_);
lean_dec(v_i_5212_);
v_stop_boxed_5221_ = lean_unbox_usize(v_stop_5213_);
lean_dec(v_stop_5213_);
v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_5206_, v_00_u03b2_5207_, v_00_u03c3_5208_, v_00_u03c3_5209_, v_f_5210_, v_as_5211_, v_i_boxed_5220_, v_stop_boxed_5221_, v_b_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec_ref(v_as_5211_);
return v_res_5222_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_5223_, lean_object* v_00_u03c3_5224_, lean_object* v_00_u03b1_5225_, lean_object* v_00_u03b2_5226_, lean_object* v_f_5227_, lean_object* v_keys_5228_, lean_object* v_vals_5229_, lean_object* v_heq_5230_, lean_object* v_i_5231_, lean_object* v_acc_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v___x_5238_; 
v___x_5238_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_5227_, v_keys_5228_, v_vals_5229_, v_i_5231_, v_acc_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
return v___x_5238_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5227_ = stack[4].m_obj;
lean_object* v_keys_5228_ = stack[5].m_obj;
lean_object* v_vals_5229_ = stack[6].m_obj;
lean_object* v_i_5231_ = stack[8].m_obj;
lean_object* v_acc_5232_ = stack[9].m_obj;
lean_object* v___y_5233_ = stack[10].m_obj;
lean_object* v___y_5234_ = stack[11].m_obj;
lean_object* v___y_5235_ = stack[12].m_obj;
lean_object* v___y_5236_ = stack[13].m_obj;
lean_object* v_res_5239_;
v_res_5239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_5227_, v_keys_5228_, v_vals_5229_, lean_box(0), v_i_5231_, v_acc_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
stack->m_obj
 = v_res_5239_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_5240_, lean_object* v_00_u03c3_5241_, lean_object* v_00_u03b1_5242_, lean_object* v_00_u03b2_5243_, lean_object* v_f_5244_, lean_object* v_keys_5245_, lean_object* v_vals_5246_, lean_object* v_heq_5247_, lean_object* v_i_5248_, lean_object* v_acc_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_5240_, v_00_u03c3_5241_, v_00_u03b1_5242_, v_00_u03b2_5243_, v_f_5244_, v_keys_5245_, v_vals_5246_, v_heq_5247_, v_i_5248_, v_acc_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
lean_dec_ref(v_vals_5246_);
lean_dec_ref(v_keys_5245_);
return v_res_5255_;
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
