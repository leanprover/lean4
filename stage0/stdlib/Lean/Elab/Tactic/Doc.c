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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object*, lean_object*);
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
size_t v_sz_boxed_53_; size_t v___x_6059__boxed_54_; lean_object* v_res_55_; 
v_sz_boxed_53_ = lean_unbox_usize(v_sz_46_);
lean_dec(v_sz_46_);
v___x_6059__boxed_54_ = lean_unbox_usize(v___x_47_);
lean_dec(v___x_47_);
v_res_55_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(v_x_45_, v_sz_boxed_53_, v___x_6059__boxed_54_, v_content_48_, v___y_49_, v___y_50_, v___y_51_);
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
lean_object* v_v_561_; lean_object* v___x_562_; lean_object* v_term_563_; lean_object* v_desc_564_; lean_object* v___x_565_; lean_object* v_bs_x27_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_v_561_ = lean_array_uget_borrowed(v_bs_554_, v_i_553_);
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
v_term_563_ = lean_ctor_get(v_v_561_, 0);
lean_inc_ref(v_term_563_);
v_desc_564_ = lean_ctor_get(v_v_561_, 1);
lean_inc_ref(v_desc_564_);
v___x_565_ = lean_unsigned_to_nat(0u);
v_bs_x27_566_ = lean_array_uset(v_bs_554_, v_i_553_, v___x_565_);
v___x_567_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_567_, 0, v_term_563_);
v___x_568_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_562_, v___x_567_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v_sz_570_ = lean_array_size(v_desc_564_);
v___x_571_ = ((size_t)0ULL);
lean_inc_ref(v_desc_564_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_570_, v___x_571_, v_desc_564_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___y_575_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__2));
v___x_586_ = lean_unsigned_to_nat(2u);
v___x_587_ = lean_mk_empty_array_with_capacity(v___x_586_);
v___x_588_ = lean_array_push(v___x_587_, v_a_569_);
v___x_589_ = lean_array_push(v___x_588_, v___x_585_);
v___x_590_ = l_Lean_Doc_joinInlines(v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = lean_array_get_size(v_desc_564_);
lean_dec_ref(v_desc_564_);
v___x_592_ = lean_nat_dec_le(v___x_591_, v___x_583_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_array_push(v___x_584_, v___x_590_);
v___x_594_ = l_Array_append___redArg(v___x_593_, v_a_573_);
lean_dec(v_a_573_);
v___x_595_ = l_Lean_Doc_joinBlocks(v___x_594_);
lean_dec_ref(v___x_594_);
v___y_575_ = v___x_595_;
goto v___jp_574_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec_ref(v___x_584_);
v___x_596_ = l_Lean_Doc_joinBlocks(v_a_573_);
lean_dec(v_a_573_);
v___x_597_ = l_Array_append___redArg(v___x_590_, v___x_596_);
lean_dec_ref(v___x_596_);
v___y_575_ = v___x_597_;
goto v___jp_574_;
}
v___jp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__0));
v___x_577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___closed__1));
v___x_578_ = l_Lean_Doc_prefixListLines(v___x_576_, v___x_577_, v___y_575_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_553_, v___x_579_);
v___x_581_ = lean_array_uset(v_bs_x27_566_, v_i_553_, v___x_578_);
v_i_553_ = v___x_580_;
v_bs_554_ = v___x_581_;
goto _start;
}
}
else
{
lean_dec(v_a_569_);
lean_dec_ref(v_bs_x27_566_);
lean_dec_ref(v_desc_564_);
return v___x_572_;
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_bs_x27_566_);
lean_dec_ref(v_desc_564_);
v_a_598_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_568_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_568_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed(lean_object* v_x_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_x_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed(lean_object* v_sz_615_, lean_object* v___x_616_, lean_object* v_content_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
size_t v_sz_boxed_622_; size_t v___x_6921__boxed_623_; lean_object* v_res_624_; 
v_sz_boxed_622_ = lean_unbox_usize(v_sz_615_);
lean_dec(v_sz_615_);
v___x_6921__boxed_623_ = lean_unbox_usize(v___x_616_);
lean_dec(v___x_616_);
v_res_624_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(v_sz_boxed_622_, v___x_6921__boxed_623_, v_content_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(lean_object* v_x_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
switch(lean_obj_tag(v_x_625_))
{
case 0:
{
lean_object* v_contents_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_639_; 
v_contents_630_ = lean_ctor_get(v_x_625_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_639_ == 0)
{
v___x_632_ = v_x_625_;
v_isShared_633_ = v_isSharedCheck_639_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_contents_630_);
lean_dec(v_x_625_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_639_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 9);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_contents_630_);
v___x_636_ = v_reuseFailAlloc_638_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_634_, v___x_636_, v_a_626_, v_a_627_, v_a_628_);
return v___x_637_;
}
}
}
case 1:
{
lean_object* v_content_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_content_640_ = lean_ctor_get(v_x_625_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v_x_625_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_content_640_);
lean_dec(v_x_625_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 0);
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
case 2:
{
lean_object* v_items_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_items_649_ = lean_ctor_get(v_x_625_, 0);
lean_inc_ref(v_items_649_);
lean_dec_ref_known(v_x_625_, 1);
v_sz_650_ = lean_array_size(v_items_649_);
v___x_651_ = ((size_t)0ULL);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_650_, v___x_651_, v_items_649_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = l_Lean_Doc_joinBlocks(v_a_653_);
lean_dec(v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_652_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_652_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
case 3:
{
lean_object* v_start_670_; lean_object* v_items_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_705_; 
v_start_670_ = lean_ctor_get(v_x_625_, 0);
v_items_671_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_705_ == 0)
{
v___x_673_ = v_x_625_;
v_isShared_674_ = v_isSharedCheck_705_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_items_671_);
lean_inc(v_start_670_);
lean_dec(v_x_625_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_705_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_out_675_; lean_object* v___y_677_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_out_675_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__2));
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = l_Int_toNat(v_start_670_);
lean_dec(v_start_670_);
v___x_704_ = lean_nat_dec_le(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_dec(v___x_703_);
v___y_677_ = v___x_702_;
goto v___jp_676_;
}
else
{
v___y_677_ = v___x_703_;
goto v___jp_676_;
}
v___jp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 1, v___y_677_);
lean_ctor_set(v___x_673_, 0, v_out_675_);
v___x_679_ = v___x_673_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_out_675_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___y_677_);
v___x_679_ = v_reuseFailAlloc_701_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
size_t v_sz_680_; size_t v___x_681_; lean_object* v___x_682_; 
v_sz_680_ = lean_array_size(v_items_671_);
v___x_681_ = ((size_t)0ULL);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_items_671_, v_sz_680_, v___x_681_, v___x_679_, v_a_626_, v_a_627_, v_a_628_);
lean_dec_ref(v_items_671_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_692_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_692_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_fst_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_fst_687_ = lean_ctor_get(v_a_683_, 0);
lean_inc(v_fst_687_);
lean_dec(v_a_683_);
v___x_688_ = l_Lean_Doc_joinBlocks(v_fst_687_);
lean_dec(v_fst_687_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_682_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_682_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_706_; size_t v_sz_707_; size_t v___x_708_; lean_object* v___x_709_; 
v_items_706_ = lean_ctor_get(v_x_625_, 0);
lean_inc_ref(v_items_706_);
lean_dec_ref_known(v_x_625_, 1);
v_sz_707_ = lean_array_size(v_items_706_);
v___x_708_ = ((size_t)0ULL);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_707_, v___x_708_, v_items_706_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_718_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = l_Lean_Doc_joinBlocks(v_a_710_);
lean_dec(v_a_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_709_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_709_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
case 5:
{
lean_object* v_items_727_; size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; 
v_items_727_ = lean_ctor_get(v_x_625_, 0);
lean_inc_ref(v_items_727_);
lean_dec_ref_known(v_x_625_, 1);
v_sz_728_ = lean_array_size(v_items_727_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_728_, v___x_729_, v_items_727_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_741_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_735_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__0));
v___x_736_ = l_Lean_Doc_joinBlocks(v_a_731_);
lean_dec(v_a_731_);
v___x_737_ = l_Lean_Doc_prefixLines(v___x_735_, v___x_736_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_737_);
v___x_739_ = v___x_733_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
v_a_742_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_730_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_730_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
case 6:
{
lean_object* v_content_750_; size_t v_sz_751_; size_t v___x_752_; lean_object* v___x_753_; 
v_content_750_ = lean_ctor_get(v_x_625_, 0);
lean_inc_ref(v_content_750_);
lean_dec_ref_known(v_x_625_, 1);
v_sz_751_ = lean_array_size(v_content_750_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_751_, v___x_752_, v_content_750_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_Lean_Doc_joinBlocks(v_a_754_);
lean_dec(v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
v_a_763_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_753_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_753_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
default: 
{
lean_object* v_container_771_; 
v_container_771_ = lean_ctor_get(v_x_625_, 0);
if (lean_obj_tag(v_container_771_) == 0)
{
lean_object* v_content_772_; lean_object* v_val_773_; lean_object* v___x_774_; lean_object* v___x_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_fallback_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref(v_container_771_);
v_content_772_ = lean_ctor_get(v_x_625_, 1);
lean_inc_ref_n(v_content_772_, 2);
lean_dec_ref_known(v_x_625_, 2);
v_val_773_ = lean_ctor_get(v_container_771_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_container_771_, 1);
v___x_774_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___closed__1));
v___x_775_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed), 5, 0);
v_sz_776_ = lean_array_size(v_content_772_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_box_usize(v_sz_776_);
v___x_779_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed__const__1));
v_fallback_780_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0___boxed), 7, 3);
lean_closure_set(v_fallback_780_, 0, v___x_778_);
lean_closure_set(v_fallback_780_, 1, v___x_779_);
lean_closure_set(v_fallback_780_, 2, v_content_772_);
v___x_781_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_773_);
v___x_782_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_781_, v_a_627_, v_a_628_);
lean_dec(v___x_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
if (lean_obj_tag(v_a_783_) == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v_fallback_780_);
lean_dec_ref(v___x_775_);
lean_dec(v_val_773_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_776_, v___x_777_, v_content_772_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_793_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = l_Lean_Doc_joinBlocks(v_a_785_);
lean_dec(v_a_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_784_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_784_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_val_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_val_802_ = lean_ctor_get(v_a_783_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v_a_783_, 1);
v___x_803_ = lean_apply_4(v_val_802_, v___x_774_, v___x_775_, v_val_773_, v_content_772_);
v___x_804_ = l_Lean_Doc_withRendererFallback(v_fallback_780_, v___x_803_, v_a_626_, v_a_627_, v_a_628_);
return v___x_804_;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_fallback_780_);
lean_dec_ref(v___x_775_);
lean_dec(v_val_773_);
lean_dec_ref(v_content_772_);
v_a_805_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_782_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_782_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_content_813_; size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_816_; 
v_content_813_ = lean_ctor_get(v_x_625_, 1);
lean_inc_ref(v_content_813_);
lean_dec_ref_known(v_x_625_, 2);
v_sz_814_ = lean_array_size(v_content_813_);
v___x_815_ = ((size_t)0ULL);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_814_, v___x_815_, v_content_813_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = l_Lean_Doc_joinBlocks(v_a_817_);
lean_dec(v_a_817_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_816_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(size_t v_sz_834_, size_t v_i_835_, lean_object* v_bs_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = lean_usize_dec_lt(v_i_835_, v_sz_834_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v_bs_836_);
return v___x_842_;
}
else
{
lean_object* v_v_843_; lean_object* v___x_844_; lean_object* v_bs_x27_845_; lean_object* v___x_846_; 
v_v_843_ = lean_array_uget(v_bs_836_, v_i_835_);
v___x_844_ = lean_unsigned_to_nat(0u);
v_bs_x27_845_ = lean_array_uset(v_bs_836_, v_i_835_, v___x_844_);
v___x_846_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_v_843_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_add(v_i_835_, v___x_848_);
v___x_850_ = lean_array_uset(v_bs_x27_845_, v_i_835_, v_a_847_);
v_i_835_ = v___x_849_;
v_bs_836_ = v___x_850_;
goto _start;
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v_bs_x27_845_);
v_a_852_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_846_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_846_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___lam__0(size_t v_sz_860_, size_t v___x_861_, lean_object* v_content_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_860_, v___x_861_, v_content_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_Doc_joinBlocks(v_a_868_);
lean_dec(v_a_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_867_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_867_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7___boxed(lean_object* v_sz_885_, lean_object* v_i_886_, lean_object* v_bs_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v_i_boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_885_);
lean_dec(v_sz_885_);
v_i_boxed_893_ = lean_unbox_usize(v_i_886_);
lean_dec(v_i_886_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v_sz_boxed_892_, v_i_boxed_893_, v_bs_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___boxed(lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_bs_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
size_t v_sz_boxed_902_; size_t v_i_boxed_903_; lean_object* v_res_904_; 
v_sz_boxed_902_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_903_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_sz_boxed_902_, v_i_boxed_903_, v_bs_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10___boxed(lean_object* v_as_905_, lean_object* v_sz_906_, lean_object* v_i_907_, lean_object* v_b_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
size_t v_sz_boxed_913_; size_t v_i_boxed_914_; lean_object* v_res_915_; 
v_sz_boxed_913_ = lean_unbox_usize(v_sz_906_);
lean_dec(v_sz_906_);
v_i_boxed_914_ = lean_unbox_usize(v_i_907_);
lean_dec(v_i_907_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__10(v_as_905_, v_sz_boxed_913_, v_i_boxed_914_, v_b_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v_as_905_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___boxed(lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_bs_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_924_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11(v_sz_boxed_923_, v_i_boxed_924_, v_bs_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(size_t v_sz_926_, size_t v_i_927_, lean_object* v_bs_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v_bs_928_);
return v___x_934_;
}
else
{
lean_object* v_v_935_; lean_object* v___x_936_; lean_object* v_bs_x27_937_; lean_object* v___x_938_; 
v_v_935_ = lean_array_uget(v_bs_928_, v_i_927_);
v___x_936_ = lean_unsigned_to_nat(0u);
v_bs_x27_937_ = lean_array_uset(v_bs_928_, v_i_927_, v___x_936_);
v___x_938_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_v_935_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = ((size_t)1ULL);
v___x_941_ = lean_usize_add(v_i_927_, v___x_940_);
v___x_942_ = lean_array_uset(v_bs_x27_937_, v_i_927_, v_a_939_);
v_i_927_ = v___x_941_;
v_bs_928_ = v___x_942_;
goto _start;
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_bs_x27_937_);
v_a_944_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_938_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_938_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed(lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_bs_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_960_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_boxed_959_, v_i_boxed_960_, v_bs_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v_zero_964_; uint8_t v_isZero_965_; 
v_zero_964_ = lean_unsigned_to_nat(0u);
v_isZero_965_ = lean_nat_dec_eq(v_x_962_, v_zero_964_);
if (v_isZero_965_ == 1)
{
lean_dec(v_x_962_);
return v_x_963_;
}
else
{
uint32_t v___x_966_; lean_object* v_one_967_; lean_object* v_n_968_; lean_object* v___x_969_; 
v___x_966_ = 35;
v_one_967_ = lean_unsigned_to_nat(1u);
v_n_968_ = lean_nat_sub(v_x_962_, v_one_967_);
lean_dec(v_x_962_);
v___x_969_ = lean_string_push(v_x_963_, v___x_966_);
v_x_962_ = v_n_968_;
v_x_963_ = v___x_969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(size_t v_sz_971_, size_t v_i_972_, lean_object* v_bs_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_972_, v_sz_971_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v_bs_973_);
return v___x_979_;
}
else
{
lean_object* v_v_980_; lean_object* v___x_981_; lean_object* v_bs_x27_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_v_980_ = lean_array_uget(v_bs_973_, v_i_972_);
v___x_981_ = lean_unsigned_to_nat(0u);
v_bs_x27_982_ = lean_array_uset(v_bs_973_, v_i_972_, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__11___closed__0));
v___x_984_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v___x_983_, v_v_980_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_972_, v___x_986_);
v___x_988_ = lean_array_uset(v_bs_x27_982_, v_i_972_, v_a_985_);
v_i_972_ = v___x_987_;
v_bs_973_ = v___x_988_;
goto _start;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_bs_x27_982_);
v_a_990_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_984_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_984_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___boxed(lean_object* v_sz_998_, lean_object* v_i_999_, lean_object* v_bs_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_998_);
lean_dec(v_sz_998_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(lean_object* v_level_1009_, lean_object* v_part_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_title_1015_; lean_object* v_content_1016_; lean_object* v_subParts_1017_; size_t v_sz_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v_title_1015_ = lean_ctor_get(v_part_1010_, 0);
lean_inc_ref(v_title_1015_);
v_content_1016_ = lean_ctor_get(v_part_1010_, 3);
lean_inc_ref(v_content_1016_);
v_subParts_1017_ = lean_ctor_get(v_part_1010_, 4);
lean_inc_ref(v_subParts_1017_);
lean_dec_ref(v_part_1010_);
v_sz_1018_ = lean_array_size(v_title_1015_);
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_sz_1018_, v___x_1019_, v_title_1015_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; size_t v_sz_1033_; lean_object* v___x_1034_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_level_1009_, v___x_1023_);
lean_inc(v___x_1024_);
v___x_1025_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__4(v___x_1024_, v___x_1022_);
v___x_1026_ = ((lean_object*)(l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___closed__0));
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
v___x_1028_ = lean_mk_empty_array_with_capacity(v___x_1023_);
lean_inc_ref_n(v___x_1028_, 2);
v___x_1029_ = lean_array_push(v___x_1028_, v___x_1027_);
v___x_1030_ = lean_array_push(v___x_1028_, v___x_1029_);
v___x_1031_ = l_Array_append___redArg(v___x_1030_, v_a_1021_);
lean_dec(v_a_1021_);
v___x_1032_ = l_Lean_Doc_joinInlines(v___x_1031_);
lean_dec_ref(v___x_1031_);
v_sz_1033_ = lean_array_size(v_content_1016_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_1033_, v___x_1019_, v_content_1016_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; size_t v_sz_1036_; lean_object* v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v_sz_1036_ = lean_array_size(v_subParts_1017_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1024_, v_sz_1036_, v___x_1019_, v_subParts_1017_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v___x_1024_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1042_ = lean_array_push(v___x_1028_, v___x_1032_);
v___x_1043_ = l_Array_append___redArg(v___x_1042_, v_a_1035_);
lean_dec(v_a_1035_);
v___x_1044_ = l_Array_append___redArg(v___x_1043_, v_a_1038_);
lean_dec(v_a_1038_);
v___x_1045_ = l_Lean_Doc_joinBlocks(v___x_1044_);
lean_dec_ref(v___x_1044_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1045_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1035_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1028_);
v_a_1050_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1037_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1037_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1028_);
lean_dec(v___x_1024_);
lean_dec_ref(v_subParts_1017_);
v_a_1058_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1034_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1034_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_subParts_1017_);
lean_dec_ref(v_content_1016_);
v_a_1066_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1020_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1020_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(lean_object* v___x_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_bs_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_bs_1077_);
return v___x_1083_;
}
else
{
lean_object* v_v_1084_; lean_object* v___x_1085_; lean_object* v_bs_x27_1086_; lean_object* v___x_1087_; 
v_v_1084_ = lean_array_uget(v_bs_1077_, v_i_1076_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v_bs_x27_1086_ = lean_array_uset(v_bs_1077_, v_i_1076_, v___x_1085_);
v___x_1087_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v___x_1074_, v_v_1084_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_add(v_i_1076_, v___x_1089_);
v___x_1091_ = lean_array_uset(v_bs_x27_1086_, v_i_1076_, v_a_1088_);
v_i_1076_ = v___x_1090_;
v_bs_1077_ = v___x_1091_;
goto _start;
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v_bs_x27_1086_);
v_a_1093_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1087_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1087_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg___boxed(lean_object* v___x_1101_, lean_object* v_sz_1102_, lean_object* v_i_1103_, lean_object* v_bs_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
size_t v_sz_boxed_1109_; size_t v_i_boxed_1110_; lean_object* v_res_1111_; 
v_sz_boxed_1109_ = lean_unbox_usize(v_sz_1102_);
lean_dec(v_sz_1102_);
v_i_boxed_1110_ = lean_unbox_usize(v_i_1103_);
lean_dec(v_i_1103_);
v_res_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__5___redArg(v___x_1101_, v_sz_boxed_1109_, v_i_boxed_1110_, v_bs_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v___x_1101_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg___boxed(lean_object* v_level_1112_, lean_object* v_part_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v_level_1112_, v_part_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec(v_level_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(size_t v_sz_1119_, size_t v_i_1120_, lean_object* v_bs_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_lt(v_i_1120_, v_sz_1119_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_bs_1121_);
return v___x_1127_;
}
else
{
lean_object* v_v_1128_; lean_object* v___x_1129_; lean_object* v_bs_x27_1130_; lean_object* v___x_1131_; 
v_v_1128_ = lean_array_uget(v_bs_1121_, v_i_1120_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v_bs_x27_1130_ = lean_array_uset(v_bs_1121_, v_i_1120_, v___x_1129_);
v___x_1131_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___redArg(v___x_1129_, v_v_1128_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_i_1120_, v___x_1133_);
v___x_1135_ = lean_array_uset(v_bs_x27_1130_, v_i_1120_, v_a_1132_);
v_i_1120_ = v___x_1134_;
v_bs_1121_ = v___x_1135_;
goto _start;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_bs_x27_1130_);
v_a_1137_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1131_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1131_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4___boxed(lean_object* v_sz_1145_, lean_object* v_i_1146_, lean_object* v_bs_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
size_t v_sz_boxed_1152_; size_t v_i_boxed_1153_; lean_object* v_res_1154_; 
v_sz_boxed_1152_ = lean_unbox_usize(v_sz_1145_);
lean_dec(v_sz_1145_);
v_i_boxed_1153_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_boxed_1152_, v_i_boxed_1153_, v_bs_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(lean_object* v_fst_1155_, lean_object* v_snd_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
size_t v_sz_1161_; size_t v___x_1162_; lean_object* v___x_1163_; 
v_sz_1161_ = lean_array_size(v_fst_1155_);
v___x_1162_ = ((size_t)0ULL);
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_sz_1161_, v___x_1162_, v_fst_1155_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; size_t v_sz_1165_; lean_object* v___x_1166_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v_sz_1165_ = lean_array_size(v_snd_1156_);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_1165_, v___x_1162_, v_snd_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = l_Array_append___redArg(v_a_1164_, v_a_1167_);
lean_dec(v_a_1167_);
v___x_1172_ = l_Lean_Doc_joinBlocks(v___x_1171_);
lean_dec_ref(v___x_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1164_);
v_a_1177_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1166_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1166_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_snd_1156_);
v_a_1185_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1163_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1163_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed(lean_object* v_fst_1193_, lean_object* v_snd_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(v_fst_1193_, v_snd_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
return v_res_1199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1203_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_ctor_set(v___x_1206_, 2, v___x_1205_);
lean_ctor_set(v___x_1206_, 3, v___x_1205_);
lean_ctor_set(v___x_1206_, 4, v___x_1204_);
lean_ctor_set(v___x_1206_, 5, v___x_1204_);
lean_ctor_set(v___x_1206_, 6, v___x_1204_);
lean_ctor_set(v___x_1206_, 7, v___x_1204_);
lean_ctor_set(v___x_1206_, 8, v___x_1204_);
lean_ctor_set(v___x_1206_, 9, v___x_1204_);
lean_ctor_set(v___x_1206_, 10, v___x_1204_);
lean_ctor_set(v___x_1206_, 11, v___x_1203_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_unsigned_to_nat(32u);
v___x_1208_ = lean_mk_empty_array_with_capacity(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1210_ = ((size_t)5ULL);
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_unsigned_to_nat(32u);
v___x_1213_ = lean_mk_empty_array_with_capacity(v___x_1212_);
v___x_1214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__3);
v___x_1215_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
lean_ctor_set(v___x_1215_, 2, v___x_1211_);
lean_ctor_set(v___x_1215_, 3, v___x_1211_);
lean_ctor_set_usize(v___x_1215_, 4, v___x_1210_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_box(1);
v___x_1217_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_1218_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__1);
v___x_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1217_);
lean_ctor_set(v___x_1219_, 2, v___x_1216_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_msgData_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v_env_1224_; uint8_t v___x_1225_; lean_object* v_env_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_scopes_1229_; lean_object* v___x_1230_; lean_object* v_opts_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1223_ = lean_st_ref_get(v___y_1221_);
v_env_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc_ref(v_env_1224_);
lean_dec(v___x_1223_);
v___x_1225_ = 0;
v_env_1226_ = l_Lean_Environment_setRecordingDeps(v_env_1224_, v___x_1225_);
v___x_1227_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1228_ = lean_st_ref_get(v___y_1221_);
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
lean_ctor_set(v___x_1235_, 1, v_msgData_1220_);
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
lean_dec(v_pre_1418_);
lean_dec_ref_known(v_pre_1417_, 2);
lean_dec_ref_known(v_pre_1416_, 2);
lean_dec_ref_known(v_kind_1415_, 2);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec_ref_known(v_pre_1416_, 2);
lean_dec(v_pre_1417_);
lean_dec_ref_known(v_kind_1415_, 2);
lean_dec_ref_known(v___x_1414_, 3);
goto v___jp_1407_;
}
}
else
{
lean_dec(v_pre_1416_);
lean_dec_ref_known(v_kind_1415_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1(lean_object* v_addEntryFn_1603_, lean_object* v___x_1604_, lean_object* v_s_1605_){
_start:
{
lean_object* v_importedEntries_1606_; lean_object* v_state_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1615_; 
v_importedEntries_1606_ = lean_ctor_get(v_s_1605_, 0);
v_state_1607_ = lean_ctor_get(v_s_1605_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_s_1605_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1609_ = v_s_1605_;
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_state_1607_);
lean_inc(v_importedEntries_1606_);
lean_dec(v_s_1605_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_state_1611_; lean_object* v___x_1613_; 
v_state_1611_ = lean_apply_2(v_addEntryFn_1603_, v_state_1607_, v___x_1604_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v_state_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_importedEntries_1606_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_state_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_1624_ = l_Lean_stringToMessageData(v___x_1623_);
return v___x_1624_;
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
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___y_1651_; lean_object* v_messages_1652_; lean_object* v_scopes_1653_; lean_object* v_usedQuotCtxts_1654_; lean_object* v_nextMacroScope_1655_; lean_object* v_maxRecDepth_1656_; lean_object* v_ngen_1657_; lean_object* v_auxDeclNGen_1658_; lean_object* v_infoState_1659_; lean_object* v_traceState_1660_; lean_object* v_snapshotTasks_1661_; lean_object* v_prevLinterStates_1662_; lean_object* v_codeQualityEntryTasks_1663_; lean_object* v___y_1664_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
lean_inc(v_x_1646_);
v___x_1670_ = l_Lean_Syntax_isOfKind(v_x_1646_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v_x_1646_);
v___x_1671_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1672_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1671_, v_a_1647_, v_a_1648_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1673_);
lean_inc(v___x_1674_);
v___x_1675_ = l_Lean_Syntax_matchesNull(v___x_1674_, v___x_1673_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1674_);
v___x_1677_ = l_Lean_Syntax_matchesNull(v___x_1674_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1674_);
lean_dec(v_x_1646_);
v___x_1678_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1678_, v_a_1647_, v_a_1648_);
return v___x_1679_;
}
else
{
lean_object* v_docs_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_docs_1680_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_1673_);
lean_dec(v___x_1674_);
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
lean_inc(v_docs_1680_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v_docs_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v_docs_1680_);
lean_dec(v_x_1646_);
v___x_1683_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1684_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1683_, v_a_1647_, v_a_1648_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1685_ = lean_unsigned_to_nat(2u);
v___x_1686_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1685_);
lean_dec(v_x_1646_);
v___x_1687_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7));
lean_inc(v___x_1686_);
v___x_1688_ = l_Lean_Syntax_isOfKind(v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v___x_1686_);
lean_dec(v_docs_1680_);
v___x_1689_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1690_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1689_, v_a_1647_, v_a_1648_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(0);
lean_inc(v___x_1686_);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1692_, 0, v___x_1686_);
lean_closure_set(v___f_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1692_, v_a_1647_, v_a_1648_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___x_1745_; lean_object* v_env_1746_; lean_object* v___x_1747_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc_n(v_a_1694_, 2);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1745_ = lean_st_ref_get(v_a_1648_);
v_env_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc_ref(v_env_1746_);
lean_dec(v___x_1745_);
v___x_1747_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1746_, v_a_1694_);
if (lean_obj_tag(v___x_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_docs_1680_);
v_val_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_1750_ = l_Lean_MessageData_ofConstName(v_a_1694_, v___x_1675_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_MessageData_ofConstName(v_val_1748_, v___x_1675_);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1749_);
v___x_1757_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___x_1686_, v___x_1756_, v_a_1647_, v_a_1648_);
lean_dec(v___x_1686_);
return v___x_1757_;
}
else
{
lean_dec(v___x_1747_);
v___y_1734_ = v_a_1647_;
v___y_1735_ = v_a_1648_;
goto v___jp_1733_;
}
v___jp_1695_:
{
lean_object* v___x_1698_; 
v___x_1698_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_docs_1680_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v_env_1701_; lean_object* v_messages_1702_; lean_object* v_scopes_1703_; lean_object* v_usedQuotCtxts_1704_; lean_object* v_nextMacroScope_1705_; lean_object* v_maxRecDepth_1706_; lean_object* v_ngen_1707_; lean_object* v_auxDeclNGen_1708_; lean_object* v_infoState_1709_; lean_object* v_traceState_1710_; lean_object* v_snapshotTasks_1711_; lean_object* v_prevLinterStates_1712_; lean_object* v_codeQualityEntryTasks_1713_; lean_object* v___x_1714_; lean_object* v_toEnvExtension_1715_; lean_object* v_addEntryFn_1716_; lean_object* v_asyncMode_1717_; uint8_t v_logWrites_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = lean_st_ref_take(v___y_1697_);
v_env_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc_ref(v_env_1701_);
v_messages_1702_ = lean_ctor_get(v___x_1700_, 1);
lean_inc_ref(v_messages_1702_);
v_scopes_1703_ = lean_ctor_get(v___x_1700_, 2);
lean_inc(v_scopes_1703_);
v_usedQuotCtxts_1704_ = lean_ctor_get(v___x_1700_, 3);
lean_inc(v_usedQuotCtxts_1704_);
v_nextMacroScope_1705_ = lean_ctor_get(v___x_1700_, 4);
lean_inc(v_nextMacroScope_1705_);
v_maxRecDepth_1706_ = lean_ctor_get(v___x_1700_, 5);
lean_inc(v_maxRecDepth_1706_);
v_ngen_1707_ = lean_ctor_get(v___x_1700_, 6);
lean_inc_ref(v_ngen_1707_);
v_auxDeclNGen_1708_ = lean_ctor_get(v___x_1700_, 7);
lean_inc_ref(v_auxDeclNGen_1708_);
v_infoState_1709_ = lean_ctor_get(v___x_1700_, 8);
lean_inc_ref(v_infoState_1709_);
v_traceState_1710_ = lean_ctor_get(v___x_1700_, 9);
lean_inc_ref(v_traceState_1710_);
v_snapshotTasks_1711_ = lean_ctor_get(v___x_1700_, 10);
lean_inc_ref(v_snapshotTasks_1711_);
v_prevLinterStates_1712_ = lean_ctor_get(v___x_1700_, 11);
lean_inc(v_prevLinterStates_1712_);
v_codeQualityEntryTasks_1713_ = lean_ctor_get(v___x_1700_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1713_);
lean_dec(v___x_1700_);
v___x_1714_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_1715_ = lean_ctor_get(v___x_1714_, 0);
v_addEntryFn_1716_ = lean_ctor_get(v___x_1714_, 3);
v_asyncMode_1717_ = lean_ctor_get(v_toEnvExtension_1715_, 2);
v_logWrites_1718_ = lean_ctor_get_uint8(v_toEnvExtension_1715_, sizeof(void*)*6);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_a_1694_);
lean_ctor_set(v___x_1719_, 1, v_a_1699_);
lean_inc(v_addEntryFn_1716_);
v___f_1720_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__1), 3, 2);
lean_closure_set(v___f_1720_, 0, v_addEntryFn_1716_);
lean_closure_set(v___f_1720_, 1, v___x_1719_);
v___x_1721_ = lean_box(0);
if (v_logWrites_1718_ == 0)
{
lean_object* v___x_1722_; 
lean_inc_ref(v_toEnvExtension_1715_);
v___x_1722_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1715_, v_env_1701_, v___f_1720_, v_asyncMode_1717_, v___x_1721_, v___x_1677_);
v___y_1651_ = v___y_1697_;
v_messages_1652_ = v_messages_1702_;
v_scopes_1653_ = v_scopes_1703_;
v_usedQuotCtxts_1654_ = v_usedQuotCtxts_1704_;
v_nextMacroScope_1655_ = v_nextMacroScope_1705_;
v_maxRecDepth_1656_ = v_maxRecDepth_1706_;
v_ngen_1657_ = v_ngen_1707_;
v_auxDeclNGen_1658_ = v_auxDeclNGen_1708_;
v_infoState_1659_ = v_infoState_1709_;
v_traceState_1660_ = v_traceState_1710_;
v_snapshotTasks_1661_ = v_snapshotTasks_1711_;
v_prevLinterStates_1662_ = v_prevLinterStates_1712_;
v_codeQualityEntryTasks_1663_ = v_codeQualityEntryTasks_1713_;
v___y_1664_ = v___x_1722_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_inc_ref_n(v_toEnvExtension_1715_, 2);
v___x_1723_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1715_, v_env_1701_);
lean_dec_ref(v_env_1701_);
v___x_1724_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1715_, v___x_1723_, v___f_1720_, v_asyncMode_1717_, v___x_1721_, v___x_1677_);
v___y_1651_ = v___y_1697_;
v_messages_1652_ = v_messages_1702_;
v_scopes_1653_ = v_scopes_1703_;
v_usedQuotCtxts_1654_ = v_usedQuotCtxts_1704_;
v_nextMacroScope_1655_ = v_nextMacroScope_1705_;
v_maxRecDepth_1656_ = v_maxRecDepth_1706_;
v_ngen_1657_ = v_ngen_1707_;
v_auxDeclNGen_1658_ = v_auxDeclNGen_1708_;
v_infoState_1659_ = v_infoState_1709_;
v_traceState_1660_ = v_traceState_1710_;
v_snapshotTasks_1661_ = v_snapshotTasks_1711_;
v_prevLinterStates_1662_ = v_prevLinterStates_1712_;
v_codeQualityEntryTasks_1663_ = v_codeQualityEntryTasks_1713_;
v___y_1664_ = v___x_1724_;
goto v___jp_1650_;
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1694_);
v_a_1725_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1698_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1698_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
v___jp_1733_:
{
lean_object* v___x_1736_; lean_object* v_env_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_st_ref_get(v___y_1735_);
v_env_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_ref(v_env_1737_);
lean_dec(v___x_1736_);
v___x_1738_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1737_, v_a_1694_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_docs_1680_);
v___x_1739_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_1740_ = l_Lean_MessageData_ofConstName(v_a_1694_, v___x_1675_);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___x_1686_, v___x_1743_, v___y_1734_, v___y_1735_);
lean_dec(v___x_1686_);
return v___x_1744_;
}
else
{
lean_dec(v___x_1686_);
v___y_1696_ = v___y_1734_;
v___y_1697_ = v___y_1735_;
goto v___jp_1695_;
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v___x_1686_);
lean_dec(v_docs_1680_);
v_a_1758_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1693_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1693_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1766_; lean_object* v_cmd_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v___x_1674_);
v___x_1766_ = lean_unsigned_to_nat(1u);
v_cmd_1767_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1766_);
lean_dec(v_x_1646_);
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15);
v___x_1769_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_cmd_1767_, v___x_1768_, v_a_1647_, v_a_1648_);
lean_dec(v_cmd_1767_);
return v___x_1769_;
}
}
v___jp_1650_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1664_);
lean_ctor_set(v___x_1665_, 1, v_messages_1652_);
lean_ctor_set(v___x_1665_, 2, v_scopes_1653_);
lean_ctor_set(v___x_1665_, 3, v_usedQuotCtxts_1654_);
lean_ctor_set(v___x_1665_, 4, v_nextMacroScope_1655_);
lean_ctor_set(v___x_1665_, 5, v_maxRecDepth_1656_);
lean_ctor_set(v___x_1665_, 6, v_ngen_1657_);
lean_ctor_set(v___x_1665_, 7, v_auxDeclNGen_1658_);
lean_ctor_set(v___x_1665_, 8, v_infoState_1659_);
lean_ctor_set(v___x_1665_, 9, v_traceState_1660_);
lean_ctor_set(v___x_1665_, 10, v_snapshotTasks_1661_);
lean_ctor_set(v___x_1665_, 11, v_prevLinterStates_1662_);
lean_ctor_set(v___x_1665_, 12, v_codeQualityEntryTasks_1663_);
v___x_1666_ = lean_st_ref_put(v___y_1651_, v___x_1665_);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1786_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1787_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1789_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_1790_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1786_, v___x_1787_, v___x_1788_, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_1820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_1821_ = l_Lean_addBuiltinDeclarationRanges(v___x_1819_, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0(lean_object* v_addEntryFn_1824_, lean_object* v___x_1825_, lean_object* v_s_1826_){
_start:
{
lean_object* v_importedEntries_1827_; lean_object* v_state_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
v_importedEntries_1827_ = lean_ctor_get(v_s_1826_, 0);
v_state_1828_ = lean_ctor_get(v_s_1826_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_s_1826_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1830_ = v_s_1826_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_state_1828_);
lean_inc(v_importedEntries_1827_);
lean_dec(v_s_1826_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_state_1832_; lean_object* v___x_1834_; 
v_state_1832_ = lean_apply_2(v_addEntryFn_1824_, v_state_1828_, v___x_1825_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_state_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_importedEntries_1827_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_state_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___y_1854_; lean_object* v_messages_1855_; lean_object* v_scopes_1856_; lean_object* v_usedQuotCtxts_1857_; lean_object* v_nextMacroScope_1858_; lean_object* v_maxRecDepth_1859_; lean_object* v_ngen_1860_; lean_object* v_auxDeclNGen_1861_; lean_object* v_infoState_1862_; lean_object* v_traceState_1863_; lean_object* v_snapshotTasks_1864_; lean_object* v_prevLinterStates_1865_; lean_object* v_codeQualityEntryTasks_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___x_1872_; uint8_t v___x_1873_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v_a_1878_; lean_object* v_doc_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; 
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
lean_inc(v_x_1849_);
v___x_1873_ = l_Lean_Syntax_isOfKind(v_x_1849_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_x_1849_);
v___x_1943_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1944_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1943_, v_a_1850_, v_a_1851_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_isNone(v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1946_);
v___x_1949_ = l_Lean_Syntax_matchesNull(v___x_1946_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v___x_1946_);
lean_dec(v_x_1849_);
v___x_1950_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1950_, v_a_1850_, v_a_1851_);
return v___x_1951_;
}
else
{
lean_object* v_doc_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_doc_1952_ = l_Lean_Syntax_getArg(v___x_1946_, v___x_1945_);
lean_dec(v___x_1946_);
v___x_1953_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
lean_inc(v_doc_1952_);
v___x_1954_ = l_Lean_Syntax_isOfKind(v_doc_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v_doc_1952_);
lean_dec(v_x_1849_);
v___x_1955_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1956_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1955_, v_a_1850_, v_a_1851_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_doc_1952_);
v_doc_1909_ = v___x_1957_;
v___y_1910_ = v_a_1850_;
v___y_1911_ = v_a_1851_;
goto v___jp_1908_;
}
}
}
else
{
lean_object* v___x_1958_; 
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_doc_1909_ = v___x_1958_;
v___y_1910_ = v_a_1850_;
v___y_1911_ = v_a_1851_;
goto v___jp_1908_;
}
}
v___jp_1853_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1869_, 0, v___y_1868_);
lean_ctor_set(v___x_1869_, 1, v_messages_1855_);
lean_ctor_set(v___x_1869_, 2, v_scopes_1856_);
lean_ctor_set(v___x_1869_, 3, v_usedQuotCtxts_1857_);
lean_ctor_set(v___x_1869_, 4, v_nextMacroScope_1858_);
lean_ctor_set(v___x_1869_, 5, v_maxRecDepth_1859_);
lean_ctor_set(v___x_1869_, 6, v_ngen_1860_);
lean_ctor_set(v___x_1869_, 7, v_auxDeclNGen_1861_);
lean_ctor_set(v___x_1869_, 8, v_infoState_1862_);
lean_ctor_set(v___x_1869_, 9, v_traceState_1863_);
lean_ctor_set(v___x_1869_, 10, v_snapshotTasks_1864_);
lean_ctor_set(v___x_1869_, 11, v_prevLinterStates_1865_);
lean_ctor_set(v___x_1869_, 12, v_codeQualityEntryTasks_1866_);
v___x_1870_ = lean_st_ref_put(v___y_1867_, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___y_1854_);
return v___x_1871_;
}
v___jp_1874_:
{
lean_object* v___x_1879_; lean_object* v_env_1880_; lean_object* v_messages_1881_; lean_object* v_scopes_1882_; lean_object* v_usedQuotCtxts_1883_; lean_object* v_nextMacroScope_1884_; lean_object* v_maxRecDepth_1885_; lean_object* v_ngen_1886_; lean_object* v_auxDeclNGen_1887_; lean_object* v_infoState_1888_; lean_object* v_traceState_1889_; lean_object* v_snapshotTasks_1890_; lean_object* v_prevLinterStates_1891_; lean_object* v_codeQualityEntryTasks_1892_; lean_object* v___x_1893_; lean_object* v_toEnvExtension_1894_; lean_object* v_addEntryFn_1895_; lean_object* v_asyncMode_1896_; uint8_t v_logWrites_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; 
v___x_1879_ = lean_st_ref_take(v___y_1876_);
v_env_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_ref(v_env_1880_);
v_messages_1881_ = lean_ctor_get(v___x_1879_, 1);
lean_inc_ref(v_messages_1881_);
v_scopes_1882_ = lean_ctor_get(v___x_1879_, 2);
lean_inc(v_scopes_1882_);
v_usedQuotCtxts_1883_ = lean_ctor_get(v___x_1879_, 3);
lean_inc(v_usedQuotCtxts_1883_);
v_nextMacroScope_1884_ = lean_ctor_get(v___x_1879_, 4);
lean_inc(v_nextMacroScope_1884_);
v_maxRecDepth_1885_ = lean_ctor_get(v___x_1879_, 5);
lean_inc(v_maxRecDepth_1885_);
v_ngen_1886_ = lean_ctor_get(v___x_1879_, 6);
lean_inc_ref(v_ngen_1886_);
v_auxDeclNGen_1887_ = lean_ctor_get(v___x_1879_, 7);
lean_inc_ref(v_auxDeclNGen_1887_);
v_infoState_1888_ = lean_ctor_get(v___x_1879_, 8);
lean_inc_ref(v_infoState_1888_);
v_traceState_1889_ = lean_ctor_get(v___x_1879_, 9);
lean_inc_ref(v_traceState_1889_);
v_snapshotTasks_1890_ = lean_ctor_get(v___x_1879_, 10);
lean_inc_ref(v_snapshotTasks_1890_);
v_prevLinterStates_1891_ = lean_ctor_get(v___x_1879_, 11);
lean_inc(v_prevLinterStates_1891_);
v_codeQualityEntryTasks_1892_ = lean_ctor_get(v___x_1879_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1892_);
lean_dec(v___x_1879_);
v___x_1893_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1894_ = lean_ctor_get(v___x_1893_, 0);
v_addEntryFn_1895_ = lean_ctor_get(v___x_1893_, 3);
v_asyncMode_1896_ = lean_ctor_get(v_toEnvExtension_1894_, 2);
v_logWrites_1897_ = lean_ctor_get_uint8(v_toEnvExtension_1894_, sizeof(void*)*6);
v___x_1898_ = lean_box(0);
v___x_1899_ = l_Lean_TSyntax_getId(v___y_1875_);
lean_dec(v___y_1875_);
v___x_1900_ = l_Lean_TSyntax_getString(v___y_1877_);
lean_dec(v___y_1877_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_a_1878_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1899_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
lean_inc(v_addEntryFn_1895_);
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___lam__0), 3, 2);
lean_closure_set(v___f_1903_, 0, v_addEntryFn_1895_);
lean_closure_set(v___f_1903_, 1, v___x_1902_);
v___x_1904_ = lean_box(0);
if (v_logWrites_1897_ == 0)
{
lean_object* v___x_1905_; 
lean_inc_ref(v_toEnvExtension_1894_);
v___x_1905_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1894_, v_env_1880_, v___f_1903_, v_asyncMode_1896_, v___x_1904_, v___x_1873_);
v___y_1854_ = v___x_1898_;
v_messages_1855_ = v_messages_1881_;
v_scopes_1856_ = v_scopes_1882_;
v_usedQuotCtxts_1857_ = v_usedQuotCtxts_1883_;
v_nextMacroScope_1858_ = v_nextMacroScope_1884_;
v_maxRecDepth_1859_ = v_maxRecDepth_1885_;
v_ngen_1860_ = v_ngen_1886_;
v_auxDeclNGen_1861_ = v_auxDeclNGen_1887_;
v_infoState_1862_ = v_infoState_1888_;
v_traceState_1863_ = v_traceState_1889_;
v_snapshotTasks_1864_ = v_snapshotTasks_1890_;
v_prevLinterStates_1865_ = v_prevLinterStates_1891_;
v_codeQualityEntryTasks_1866_ = v_codeQualityEntryTasks_1892_;
v___y_1867_ = v___y_1876_;
v___y_1868_ = v___x_1905_;
goto v___jp_1853_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_inc_ref_n(v_toEnvExtension_1894_, 2);
v___x_1906_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1894_, v_env_1880_);
lean_dec_ref(v_env_1880_);
v___x_1907_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1894_, v___x_1906_, v___f_1903_, v_asyncMode_1896_, v___x_1904_, v___x_1873_);
v___y_1854_ = v___x_1898_;
v_messages_1855_ = v_messages_1881_;
v_scopes_1856_ = v_scopes_1882_;
v_usedQuotCtxts_1857_ = v_usedQuotCtxts_1883_;
v_nextMacroScope_1858_ = v_nextMacroScope_1884_;
v_maxRecDepth_1859_ = v_maxRecDepth_1885_;
v_ngen_1860_ = v_ngen_1886_;
v_auxDeclNGen_1861_ = v_auxDeclNGen_1887_;
v_infoState_1862_ = v_infoState_1888_;
v_traceState_1863_ = v_traceState_1889_;
v_snapshotTasks_1864_ = v_snapshotTasks_1890_;
v_prevLinterStates_1865_ = v_prevLinterStates_1891_;
v_codeQualityEntryTasks_1866_ = v_codeQualityEntryTasks_1892_;
v___y_1867_ = v___y_1876_;
v___y_1868_ = v___x_1907_;
goto v___jp_1853_;
}
}
v___jp_1908_:
{
lean_object* v___x_1912_; lean_object* v_tag_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1912_ = lean_unsigned_to_nat(2u);
v_tag_1913_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1912_);
v___x_1914_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7));
lean_inc(v_tag_1913_);
v___x_1915_ = l_Lean_Syntax_isOfKind(v_tag_1913_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_tag_1913_);
lean_dec(v_doc_1909_);
lean_dec(v_x_1849_);
v___x_1916_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1917_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1916_, v___y_1910_, v___y_1911_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v_user_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1918_ = lean_unsigned_to_nat(3u);
v_user_1919_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1918_);
lean_dec(v_x_1849_);
v___x_1920_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_user_1919_);
v___x_1921_ = l_Lean_Syntax_isOfKind(v_user_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v_user_1919_);
lean_dec(v_tag_1913_);
lean_dec(v_doc_1909_);
v___x_1922_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3);
v___x_1923_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1___redArg(v___x_1922_, v___y_1910_, v___y_1911_);
return v___x_1923_;
}
else
{
if (lean_obj_tag(v_doc_1909_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_box(0);
v___y_1875_ = v_tag_1913_;
v___y_1876_ = v___y_1911_;
v___y_1877_ = v_user_1919_;
v_a_1878_ = v___x_1924_;
goto v___jp_1874_;
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1942_; 
v_val_1925_ = lean_ctor_get(v_doc_1909_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_doc_1909_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1927_ = v_doc_1909_;
v_isShared_1928_ = v_isSharedCheck_1942_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_val_1925_);
lean_dec(v_doc_1909_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1942_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_val_1925_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v_a_1930_);
v___x_1932_ = v___x_1927_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
v___y_1875_ = v_tag_1913_;
v___y_1876_ = v___y_1911_;
v___y_1877_ = v_user_1919_;
v_a_1878_ = v___x_1932_;
goto v___jp_1874_;
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_del_object(v___x_1927_);
lean_dec(v_user_1919_);
lean_dec(v_tag_1913_);
v_a_1934_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1929_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1929_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1972_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1));
v___x_1974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_1975_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_1976_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1972_, v___x_1973_, v___x_1974_, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_2007_ = l_Lean_addBuiltinDeclarationRanges(v___x_2005_, v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_2010_, lean_object* v_x_2011_){
_start:
{
if (lean_obj_tag(v_x_2011_) == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2010_);
return v___x_2012_;
}
else
{
lean_dec_ref(v___x_2010_);
lean_inc_ref(v_x_2011_);
return v_x_2011_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2013_, v_x_2014_);
lean_dec(v_x_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_2016_, lean_object* v_k_2017_, lean_object* v_t_2018_){
_start:
{
if (lean_obj_tag(v_t_2018_) == 0)
{
lean_object* v_size_2019_; lean_object* v_k_2020_; lean_object* v_v_2021_; lean_object* v_l_2022_; lean_object* v_r_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2349_; 
v_size_2019_ = lean_ctor_get(v_t_2018_, 0);
v_k_2020_ = lean_ctor_get(v_t_2018_, 1);
v_v_2021_ = lean_ctor_get(v_t_2018_, 2);
v_l_2022_ = lean_ctor_get(v_t_2018_, 3);
v_r_2023_ = lean_ctor_get(v_t_2018_, 4);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_t_2018_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2025_ = v_t_2018_;
v_isShared_2026_ = v_isSharedCheck_2349_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_r_2023_);
lean_inc(v_l_2022_);
lean_inc(v_v_2021_);
lean_inc(v_k_2020_);
lean_inc(v_size_2019_);
lean_dec(v_t_2018_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2349_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; 
v___x_2027_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2017_, v_k_2020_);
switch(v___x_2027_)
{
case 0:
{
lean_object* v_impl_2028_; lean_object* v___x_2029_; 
lean_del_object(v___x_2025_);
lean_dec(v_size_2019_);
v_impl_2028_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2016_, v_k_2017_, v_l_2022_);
v___x_2029_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2020_, v_v_2021_, v_impl_2028_, v_r_2023_);
return v___x_2029_;
}
case 1:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v_k_2020_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_v_2021_);
v___x_2031_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2016_, v___x_2030_);
lean_dec_ref_known(v___x_2030_, 1);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_del_object(v___x_2025_);
lean_dec(v_size_2019_);
lean_dec(v_k_2017_);
if (lean_obj_tag(v_l_2022_) == 0)
{
if (lean_obj_tag(v_r_2023_) == 0)
{
lean_object* v_size_2032_; lean_object* v_k_2033_; lean_object* v_v_2034_; lean_object* v_l_2035_; lean_object* v_r_2036_; lean_object* v_size_2037_; lean_object* v_k_2038_; lean_object* v_v_2039_; lean_object* v_l_2040_; lean_object* v_r_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_size_2032_ = lean_ctor_get(v_l_2022_, 0);
v_k_2033_ = lean_ctor_get(v_l_2022_, 1);
v_v_2034_ = lean_ctor_get(v_l_2022_, 2);
v_l_2035_ = lean_ctor_get(v_l_2022_, 3);
v_r_2036_ = lean_ctor_get(v_l_2022_, 4);
lean_inc(v_r_2036_);
v_size_2037_ = lean_ctor_get(v_r_2023_, 0);
v_k_2038_ = lean_ctor_get(v_r_2023_, 1);
v_v_2039_ = lean_ctor_get(v_r_2023_, 2);
v_l_2040_ = lean_ctor_get(v_r_2023_, 3);
lean_inc(v_l_2040_);
v_r_2041_ = lean_ctor_get(v_r_2023_, 4);
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = lean_nat_dec_lt(v_size_2032_, v_size_2037_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2179_; 
lean_inc(v_l_2035_);
lean_inc(v_v_2034_);
lean_inc(v_k_2033_);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_l_2022_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2180_ = lean_ctor_get(v_l_2022_, 4);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_l_2022_, 3);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_l_2022_, 2);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_2022_, 1);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_2022_, 0);
lean_dec(v_unused_2184_);
v___x_2045_ = v_l_2022_;
v_isShared_2046_ = v_isSharedCheck_2179_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v_l_2022_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2179_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v_tree_2048_; 
v___x_2047_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2033_, v_v_2034_, v_l_2035_, v_r_2036_);
v_tree_2048_ = lean_ctor_get(v___x_2047_, 2);
if (lean_obj_tag(v_tree_2048_) == 0)
{
lean_object* v_k_2049_; lean_object* v_v_2050_; lean_object* v_size_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
lean_inc_ref(v_tree_2048_);
v_k_2049_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_k_2049_);
v_v_2050_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_v_2050_);
lean_dec_ref(v___x_2047_);
v_size_2051_ = lean_ctor_get(v_tree_2048_, 0);
v___x_2052_ = lean_unsigned_to_nat(3u);
v___x_2053_ = lean_nat_mul(v___x_2052_, v_size_2051_);
v___x_2054_ = lean_nat_dec_lt(v___x_2053_, v_size_2037_);
lean_dec(v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_dec(v_l_2040_);
v___x_2055_ = lean_nat_add(v___x_2042_, v_size_2051_);
v___x_2056_ = lean_nat_add(v___x_2055_, v_size_2037_);
lean_dec(v___x_2055_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_r_2023_);
lean_ctor_set(v___x_2045_, 3, v_tree_2048_);
lean_ctor_set(v___x_2045_, 2, v_v_2050_);
lean_ctor_set(v___x_2045_, 1, v_k_2049_);
lean_ctor_set(v___x_2045_, 0, v___x_2056_);
v___x_2058_ = v___x_2045_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_tree_2048_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_r_2023_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
else
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2114_; 
lean_inc(v_r_2041_);
lean_inc(v_v_2039_);
lean_inc(v_k_2038_);
lean_inc(v_size_2037_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_r_2023_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; 
v_unused_2115_ = lean_ctor_get(v_r_2023_, 4);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_r_2023_, 3);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_r_2023_, 2);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_r_2023_, 1);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_r_2023_, 0);
lean_dec(v_unused_2119_);
v___x_2061_ = v_r_2023_;
v_isShared_2062_ = v_isSharedCheck_2114_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_r_2023_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2114_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_size_2063_; lean_object* v_k_2064_; lean_object* v_v_2065_; lean_object* v_l_2066_; lean_object* v_r_2067_; lean_object* v_size_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_size_2063_ = lean_ctor_get(v_l_2040_, 0);
v_k_2064_ = lean_ctor_get(v_l_2040_, 1);
v_v_2065_ = lean_ctor_get(v_l_2040_, 2);
v_l_2066_ = lean_ctor_get(v_l_2040_, 3);
v_r_2067_ = lean_ctor_get(v_l_2040_, 4);
v_size_2068_ = lean_ctor_get(v_r_2041_, 0);
v___x_2069_ = lean_unsigned_to_nat(2u);
v___x_2070_ = lean_nat_mul(v___x_2069_, v_size_2068_);
v___x_2071_ = lean_nat_dec_lt(v_size_2063_, v___x_2070_);
lean_dec(v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2099_; 
lean_inc(v_r_2067_);
lean_inc(v_l_2066_);
lean_inc(v_v_2065_);
lean_inc(v_k_2064_);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_l_2040_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; lean_object* v_unused_2101_; lean_object* v_unused_2102_; lean_object* v_unused_2103_; lean_object* v_unused_2104_; 
v_unused_2100_ = lean_ctor_get(v_l_2040_, 4);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_l_2040_, 3);
lean_dec(v_unused_2101_);
v_unused_2102_ = lean_ctor_get(v_l_2040_, 2);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v_l_2040_, 1);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_l_2040_, 0);
lean_dec(v_unused_2104_);
v___x_2073_ = v_l_2040_;
v_isShared_2074_ = v_isSharedCheck_2099_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v_l_2040_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2099_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2089_; 
v___x_2075_ = lean_nat_add(v___x_2042_, v_size_2051_);
v___x_2076_ = lean_nat_add(v___x_2075_, v_size_2037_);
lean_dec(v_size_2037_);
if (lean_obj_tag(v_l_2066_) == 0)
{
lean_object* v_size_2097_; 
v_size_2097_ = lean_ctor_get(v_l_2066_, 0);
lean_inc(v_size_2097_);
v___y_2089_ = v_size_2097_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_unsigned_to_nat(0u);
v___y_2089_ = v___x_2098_;
goto v___jp_2088_;
}
v___jp_2077_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_nat_add(v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec(v___y_2079_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_r_2041_);
lean_ctor_set(v___x_2073_, 3, v_r_2067_);
lean_ctor_set(v___x_2073_, 2, v_v_2039_);
lean_ctor_set(v___x_2073_, 1, v_k_2038_);
lean_ctor_set(v___x_2073_, 0, v___x_2081_);
v___x_2083_ = v___x_2073_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_r_2067_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_r_2041_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2085_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v___x_2083_);
lean_ctor_set(v___x_2061_, 3, v___y_2078_);
lean_ctor_set(v___x_2061_, 2, v_v_2065_);
lean_ctor_set(v___x_2061_, 1, v_k_2064_);
lean_ctor_set(v___x_2061_, 0, v___x_2076_);
v___x_2085_ = v___x_2061_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v___y_2078_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_nat_add(v___x_2075_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec(v___x_2075_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_l_2066_);
lean_ctor_set(v___x_2045_, 3, v_tree_2048_);
lean_ctor_set(v___x_2045_, 2, v_v_2050_);
lean_ctor_set(v___x_2045_, 1, v_k_2049_);
lean_ctor_set(v___x_2045_, 0, v___x_2090_);
v___x_2092_ = v___x_2045_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_tree_2048_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_l_2066_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_nat_add(v___x_2042_, v_size_2068_);
if (lean_obj_tag(v_r_2067_) == 0)
{
lean_object* v_size_2094_; 
v_size_2094_ = lean_ctor_get(v_r_2067_, 0);
lean_inc(v_size_2094_);
v___y_2078_ = v___x_2092_;
v___y_2079_ = v___x_2093_;
v___y_2080_ = v_size_2094_;
goto v___jp_2077_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___y_2078_ = v___x_2092_;
v___y_2079_ = v___x_2093_;
v___y_2080_ = v___x_2095_;
goto v___jp_2077_;
}
}
}
}
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2105_ = lean_nat_add(v___x_2042_, v_size_2051_);
v___x_2106_ = lean_nat_add(v___x_2105_, v_size_2037_);
lean_dec(v_size_2037_);
v___x_2107_ = lean_nat_add(v___x_2105_, v_size_2063_);
lean_dec(v___x_2105_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_l_2040_);
lean_ctor_set(v___x_2061_, 3, v_tree_2048_);
lean_ctor_set(v___x_2061_, 2, v_v_2050_);
lean_ctor_set(v___x_2061_, 1, v_k_2049_);
lean_ctor_set(v___x_2061_, 0, v___x_2107_);
v___x_2109_ = v___x_2061_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_tree_2048_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_l_2040_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_r_2041_);
lean_ctor_set(v___x_2045_, 3, v___x_2109_);
lean_ctor_set(v___x_2045_, 2, v_v_2039_);
lean_ctor_set(v___x_2045_, 1, v_k_2038_);
lean_ctor_set(v___x_2045_, 0, v___x_2106_);
v___x_2111_ = v___x_2045_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_r_2041_);
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
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2173_; 
lean_inc(v_r_2041_);
lean_inc(v_v_2039_);
lean_inc(v_k_2038_);
lean_inc(v_size_2037_);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_r_2023_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; 
v_unused_2174_ = lean_ctor_get(v_r_2023_, 4);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_r_2023_, 3);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_r_2023_, 2);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_r_2023_, 1);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_r_2023_, 0);
lean_dec(v_unused_2178_);
v___x_2121_ = v_r_2023_;
v_isShared_2122_ = v_isSharedCheck_2173_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v_r_2023_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2173_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
if (lean_obj_tag(v_l_2040_) == 0)
{
if (lean_obj_tag(v_r_2041_) == 0)
{
lean_object* v_k_2123_; lean_object* v_v_2124_; lean_object* v_size_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_inc(v_tree_2048_);
v_k_2123_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_k_2123_);
v_v_2124_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_v_2124_);
lean_dec_ref(v___x_2047_);
v_size_2125_ = lean_ctor_get(v_l_2040_, 0);
v___x_2126_ = lean_nat_add(v___x_2042_, v_size_2037_);
lean_dec(v_size_2037_);
v___x_2127_ = lean_nat_add(v___x_2042_, v_size_2125_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 4, v_l_2040_);
lean_ctor_set(v___x_2121_, 3, v_tree_2048_);
lean_ctor_set(v___x_2121_, 2, v_v_2124_);
lean_ctor_set(v___x_2121_, 1, v_k_2123_);
lean_ctor_set(v___x_2121_, 0, v___x_2127_);
v___x_2129_ = v___x_2121_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_k_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_v_2124_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_tree_2048_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_l_2040_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_r_2041_);
lean_ctor_set(v___x_2045_, 3, v___x_2129_);
lean_ctor_set(v___x_2045_, 2, v_v_2039_);
lean_ctor_set(v___x_2045_, 1, v_k_2038_);
lean_ctor_set(v___x_2045_, 0, v___x_2126_);
v___x_2131_ = v___x_2045_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_r_2041_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
lean_object* v_k_2134_; lean_object* v_v_2135_; lean_object* v_k_2136_; lean_object* v_v_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_size_2037_);
v_k_2134_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_k_2134_);
v_v_2135_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_v_2135_);
lean_dec_ref(v___x_2047_);
v_k_2136_ = lean_ctor_get(v_l_2040_, 1);
v_v_2137_ = lean_ctor_get(v_l_2040_, 2);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_l_2040_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; lean_object* v_unused_2153_; lean_object* v_unused_2154_; 
v_unused_2152_ = lean_ctor_get(v_l_2040_, 4);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_l_2040_, 3);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v_l_2040_, 0);
lean_dec(v_unused_2154_);
v___x_2139_ = v_l_2040_;
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_v_2137_);
lean_inc(v_k_2136_);
lean_dec(v_l_2040_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_unsigned_to_nat(3u);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 4, v_r_2041_);
lean_ctor_set(v___x_2139_, 3, v_r_2041_);
lean_ctor_set(v___x_2139_, 2, v_v_2135_);
lean_ctor_set(v___x_2139_, 1, v_k_2134_);
lean_ctor_set(v___x_2139_, 0, v___x_2042_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_k_2134_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_v_2135_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_r_2041_);
v___x_2143_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2145_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 3, v_r_2041_);
lean_ctor_set(v___x_2121_, 0, v___x_2042_);
v___x_2145_ = v___x_2121_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_r_2041_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v___x_2145_);
lean_ctor_set(v___x_2045_, 3, v___x_2143_);
lean_ctor_set(v___x_2045_, 2, v_v_2137_);
lean_ctor_set(v___x_2045_, 1, v_k_2136_);
lean_ctor_set(v___x_2045_, 0, v___x_2141_);
v___x_2147_ = v___x_2045_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_2136_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_2137_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2041_) == 0)
{
lean_object* v_k_2155_; lean_object* v_v_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec(v_size_2037_);
v_k_2155_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_k_2155_);
v_v_2156_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_v_2156_);
lean_dec_ref(v___x_2047_);
v___x_2157_ = lean_unsigned_to_nat(3u);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 4, v_l_2040_);
lean_ctor_set(v___x_2121_, 2, v_v_2156_);
lean_ctor_set(v___x_2121_, 1, v_k_2155_);
lean_ctor_set(v___x_2121_, 0, v___x_2042_);
v___x_2159_ = v___x_2121_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_2155_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_2156_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_l_2040_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_r_2041_);
lean_ctor_set(v___x_2045_, 3, v___x_2159_);
lean_ctor_set(v___x_2045_, 2, v_v_2039_);
lean_ctor_set(v___x_2045_, 1, v_k_2038_);
lean_ctor_set(v___x_2045_, 0, v___x_2157_);
v___x_2161_ = v___x_2045_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_r_2041_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v_k_2164_; lean_object* v_v_2165_; lean_object* v___x_2167_; 
v_k_2164_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_k_2164_);
v_v_2165_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_v_2165_);
lean_dec_ref(v___x_2047_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 3, v_r_2041_);
v___x_2167_ = v___x_2121_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_size_2037_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_r_2041_);
v___x_2167_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_unsigned_to_nat(2u);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v___x_2167_);
lean_ctor_set(v___x_2045_, 3, v_r_2041_);
lean_ctor_set(v___x_2045_, 2, v_v_2165_);
lean_ctor_set(v___x_2045_, 1, v_k_2164_);
lean_ctor_set(v___x_2045_, 0, v___x_2168_);
v___x_2170_ = v___x_2045_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2164_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2167_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
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
lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2337_; 
lean_inc(v_r_2041_);
lean_inc(v_v_2039_);
lean_inc(v_k_2038_);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_r_2023_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; lean_object* v_unused_2339_; lean_object* v_unused_2340_; lean_object* v_unused_2341_; lean_object* v_unused_2342_; 
v_unused_2338_ = lean_ctor_get(v_r_2023_, 4);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_2023_, 3);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_r_2023_, 2);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_r_2023_, 1);
lean_dec(v_unused_2341_);
v_unused_2342_ = lean_ctor_get(v_r_2023_, 0);
lean_dec(v_unused_2342_);
v___x_2186_ = v_r_2023_;
v_isShared_2187_ = v_isSharedCheck_2337_;
goto v_resetjp_2185_;
}
else
{
lean_dec(v_r_2023_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2337_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v_tree_2189_; 
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2038_, v_v_2039_, v_l_2040_, v_r_2041_);
v_tree_2189_ = lean_ctor_get(v___x_2188_, 2);
lean_inc(v_tree_2189_);
if (lean_obj_tag(v_tree_2189_) == 0)
{
lean_object* v_k_2190_; lean_object* v_v_2191_; lean_object* v_size_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_k_2190_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_k_2190_);
v_v_2191_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_v_2191_);
lean_dec_ref(v___x_2188_);
v_size_2192_ = lean_ctor_get(v_tree_2189_, 0);
v___x_2193_ = lean_unsigned_to_nat(3u);
v___x_2194_ = lean_nat_mul(v___x_2193_, v_size_2192_);
v___x_2195_ = lean_nat_dec_lt(v___x_2194_, v_size_2032_);
lean_dec(v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_dec(v_r_2036_);
v___x_2196_ = lean_nat_add(v___x_2042_, v_size_2032_);
v___x_2197_ = lean_nat_add(v___x_2196_, v_size_2192_);
lean_dec(v___x_2196_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_tree_2189_);
lean_ctor_set(v___x_2186_, 3, v_l_2022_);
lean_ctor_set(v___x_2186_, 2, v_v_2191_);
lean_ctor_set(v___x_2186_, 1, v_k_2190_);
lean_ctor_set(v___x_2186_, 0, v___x_2197_);
v___x_2199_ = v___x_2186_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2190_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2191_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_2022_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_tree_2189_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
else
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2266_; 
lean_inc(v_l_2035_);
lean_inc(v_v_2034_);
lean_inc(v_k_2033_);
lean_inc(v_size_2032_);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_l_2022_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; 
v_unused_2267_ = lean_ctor_get(v_l_2022_, 4);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_l_2022_, 3);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_l_2022_, 2);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_l_2022_, 1);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_l_2022_, 0);
lean_dec(v_unused_2271_);
v___x_2202_ = v_l_2022_;
v_isShared_2203_ = v_isSharedCheck_2266_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v_l_2022_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2266_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_size_2204_; lean_object* v_size_2205_; lean_object* v_k_2206_; lean_object* v_v_2207_; lean_object* v_l_2208_; lean_object* v_r_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_size_2204_ = lean_ctor_get(v_l_2035_, 0);
v_size_2205_ = lean_ctor_get(v_r_2036_, 0);
v_k_2206_ = lean_ctor_get(v_r_2036_, 1);
v_v_2207_ = lean_ctor_get(v_r_2036_, 2);
v_l_2208_ = lean_ctor_get(v_r_2036_, 3);
v_r_2209_ = lean_ctor_get(v_r_2036_, 4);
v___x_2210_ = lean_unsigned_to_nat(2u);
v___x_2211_ = lean_nat_mul(v___x_2210_, v_size_2204_);
v___x_2212_ = lean_nat_dec_lt(v_size_2205_, v___x_2211_);
lean_dec(v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2250_; 
lean_inc(v_r_2209_);
lean_inc(v_l_2208_);
lean_inc(v_v_2207_);
lean_inc(v_k_2206_);
lean_del_object(v___x_2202_);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_r_2036_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; lean_object* v_unused_2252_; lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; 
v_unused_2251_ = lean_ctor_get(v_r_2036_, 4);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_r_2036_, 3);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_r_2036_, 2);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_r_2036_, 1);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_r_2036_, 0);
lean_dec(v_unused_2255_);
v___x_2214_ = v_r_2036_;
v_isShared_2215_ = v_isSharedCheck_2250_;
goto v_resetjp_2213_;
}
else
{
lean_dec(v_r_2036_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2250_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___x_2238_; lean_object* v___y_2240_; 
v___x_2216_ = lean_nat_add(v___x_2042_, v_size_2032_);
lean_dec(v_size_2032_);
v___x_2217_ = lean_nat_add(v___x_2216_, v_size_2192_);
lean_dec(v___x_2216_);
v___x_2238_ = lean_nat_add(v___x_2042_, v_size_2204_);
if (lean_obj_tag(v_l_2208_) == 0)
{
lean_object* v_size_2248_; 
v_size_2248_ = lean_ctor_get(v_l_2208_, 0);
lean_inc(v_size_2248_);
v___y_2240_ = v_size_2248_;
goto v___jp_2239_;
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_unsigned_to_nat(0u);
v___y_2240_ = v___x_2249_;
goto v___jp_2239_;
}
v___jp_2218_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = lean_nat_add(v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec(v___y_2220_);
lean_inc_ref(v_tree_2189_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 4, v_tree_2189_);
lean_ctor_set(v___x_2214_, 3, v_r_2209_);
lean_ctor_set(v___x_2214_, 2, v_v_2191_);
lean_ctor_set(v___x_2214_, 1, v_k_2190_);
lean_ctor_set(v___x_2214_, 0, v___x_2222_);
v___x_2224_ = v___x_2214_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_2190_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_2191_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_r_2209_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_tree_2189_);
v___x_2224_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
v_isSharedCheck_2231_ = !lean_is_exclusive(v_tree_2189_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; 
v_unused_2232_ = lean_ctor_get(v_tree_2189_, 4);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_tree_2189_, 3);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_tree_2189_, 2);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_tree_2189_, 1);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_tree_2189_, 0);
lean_dec(v_unused_2236_);
v___x_2226_ = v_tree_2189_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_dec(v_tree_2189_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 4, v___x_2224_);
lean_ctor_set(v___x_2226_, 3, v___y_2219_);
lean_ctor_set(v___x_2226_, 2, v_v_2207_);
lean_ctor_set(v___x_2226_, 1, v_k_2206_);
lean_ctor_set(v___x_2226_, 0, v___x_2217_);
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v___y_2219_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v___x_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
v___jp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_nat_add(v___x_2238_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec(v___x_2238_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_l_2208_);
lean_ctor_set(v___x_2186_, 3, v_l_2035_);
lean_ctor_set(v___x_2186_, 2, v_v_2034_);
lean_ctor_set(v___x_2186_, 1, v_k_2033_);
lean_ctor_set(v___x_2186_, 0, v___x_2241_);
v___x_2243_ = v___x_2186_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_k_2033_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_v_2034_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v_l_2208_);
v___x_2243_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_nat_add(v___x_2042_, v_size_2192_);
if (lean_obj_tag(v_r_2209_) == 0)
{
lean_object* v_size_2245_; 
v_size_2245_ = lean_ctor_get(v_r_2209_, 0);
lean_inc(v_size_2245_);
v___y_2219_ = v___x_2243_;
v___y_2220_ = v___x_2244_;
v___y_2221_ = v_size_2245_;
goto v___jp_2218_;
}
else
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_unsigned_to_nat(0u);
v___y_2219_ = v___x_2243_;
v___y_2220_ = v___x_2244_;
v___y_2221_ = v___x_2246_;
goto v___jp_2218_;
}
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2256_ = lean_nat_add(v___x_2042_, v_size_2032_);
lean_dec(v_size_2032_);
v___x_2257_ = lean_nat_add(v___x_2256_, v_size_2192_);
lean_dec(v___x_2256_);
v___x_2258_ = lean_nat_add(v___x_2042_, v_size_2192_);
v___x_2259_ = lean_nat_add(v___x_2258_, v_size_2205_);
lean_dec(v___x_2258_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_tree_2189_);
lean_ctor_set(v___x_2186_, 3, v_r_2036_);
lean_ctor_set(v___x_2186_, 2, v_v_2191_);
lean_ctor_set(v___x_2186_, 1, v_k_2190_);
lean_ctor_set(v___x_2186_, 0, v___x_2259_);
v___x_2261_ = v___x_2186_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_2190_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_2191_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_tree_2189_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v___x_2261_);
lean_ctor_set(v___x_2202_, 0, v___x_2257_);
v___x_2263_ = v___x_2202_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_k_2033_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_v_2034_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2035_) == 0)
{
lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2295_; 
lean_inc_ref(v_l_2035_);
lean_inc(v_v_2034_);
lean_inc(v_k_2033_);
lean_inc(v_size_2032_);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_l_2022_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; lean_object* v_unused_2297_; lean_object* v_unused_2298_; lean_object* v_unused_2299_; lean_object* v_unused_2300_; 
v_unused_2296_ = lean_ctor_get(v_l_2022_, 4);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_l_2022_, 3);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_l_2022_, 2);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_l_2022_, 1);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_l_2022_, 0);
lean_dec(v_unused_2300_);
v___x_2273_ = v_l_2022_;
v_isShared_2274_ = v_isSharedCheck_2295_;
goto v_resetjp_2272_;
}
else
{
lean_dec(v_l_2022_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2295_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
if (lean_obj_tag(v_r_2036_) == 0)
{
lean_object* v_k_2275_; lean_object* v_v_2276_; lean_object* v_size_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v_k_2275_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_k_2275_);
v_v_2276_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_v_2276_);
lean_dec_ref(v___x_2188_);
v_size_2277_ = lean_ctor_get(v_r_2036_, 0);
v___x_2278_ = lean_nat_add(v___x_2042_, v_size_2032_);
lean_dec(v_size_2032_);
v___x_2279_ = lean_nat_add(v___x_2042_, v_size_2277_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_tree_2189_);
lean_ctor_set(v___x_2186_, 3, v_r_2036_);
lean_ctor_set(v___x_2186_, 2, v_v_2276_);
lean_ctor_set(v___x_2186_, 1, v_k_2275_);
lean_ctor_set(v___x_2186_, 0, v___x_2279_);
v___x_2281_ = v___x_2186_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2275_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2276_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v_tree_2189_);
v___x_2281_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2283_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 4, v___x_2281_);
lean_ctor_set(v___x_2273_, 0, v___x_2278_);
v___x_2283_ = v___x_2273_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_2033_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_2034_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_k_2286_; lean_object* v_v_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_dec(v_size_2032_);
v_k_2286_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_k_2286_);
v_v_2287_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_v_2287_);
lean_dec_ref(v___x_2188_);
v___x_2288_ = lean_unsigned_to_nat(3u);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_r_2036_);
lean_ctor_set(v___x_2186_, 3, v_r_2036_);
lean_ctor_set(v___x_2186_, 2, v_v_2287_);
lean_ctor_set(v___x_2186_, 1, v_k_2286_);
lean_ctor_set(v___x_2186_, 0, v___x_2042_);
v___x_2290_ = v___x_2186_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v_r_2036_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 4, v___x_2290_);
lean_ctor_set(v___x_2273_, 0, v___x_2288_);
v___x_2292_ = v___x_2273_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_2033_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_2034_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2036_) == 0)
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2325_; 
lean_inc(v_l_2035_);
lean_inc(v_v_2034_);
lean_inc(v_k_2033_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_l_2022_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; lean_object* v_unused_2327_; lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; 
v_unused_2326_ = lean_ctor_get(v_l_2022_, 4);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_l_2022_, 3);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_l_2022_, 2);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_l_2022_, 1);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_l_2022_, 0);
lean_dec(v_unused_2330_);
v___x_2302_ = v_l_2022_;
v_isShared_2303_ = v_isSharedCheck_2325_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v_l_2022_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2325_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_k_2304_; lean_object* v_v_2305_; lean_object* v_k_2306_; lean_object* v_v_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2321_; 
v_k_2304_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_k_2304_);
v_v_2305_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_v_2305_);
lean_dec_ref(v___x_2188_);
v_k_2306_ = lean_ctor_get(v_r_2036_, 1);
v_v_2307_ = lean_ctor_get(v_r_2036_, 2);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_r_2036_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2322_ = lean_ctor_get(v_r_2036_, 4);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_r_2036_, 3);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_r_2036_, 0);
lean_dec(v_unused_2324_);
v___x_2309_ = v_r_2036_;
v_isShared_2310_ = v_isSharedCheck_2321_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_v_2307_);
lean_inc(v_k_2306_);
lean_dec(v_r_2036_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2321_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_unsigned_to_nat(3u);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_l_2035_);
lean_ctor_set(v___x_2309_, 3, v_l_2035_);
lean_ctor_set(v___x_2309_, 2, v_v_2034_);
lean_ctor_set(v___x_2309_, 1, v_k_2033_);
lean_ctor_set(v___x_2309_, 0, v___x_2042_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_k_2033_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_v_2034_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_l_2035_);
v___x_2313_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2315_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_l_2035_);
lean_ctor_set(v___x_2186_, 3, v_l_2035_);
lean_ctor_set(v___x_2186_, 2, v_v_2305_);
lean_ctor_set(v___x_2186_, 1, v_k_2304_);
lean_ctor_set(v___x_2186_, 0, v___x_2042_);
v___x_2315_ = v___x_2186_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_l_2035_);
v___x_2315_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2317_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 4, v___x_2315_);
lean_ctor_set(v___x_2302_, 3, v___x_2313_);
lean_ctor_set(v___x_2302_, 2, v_v_2307_);
lean_ctor_set(v___x_2302_, 1, v_k_2306_);
lean_ctor_set(v___x_2302_, 0, v___x_2311_);
v___x_2317_ = v___x_2302_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_k_2306_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_v_2307_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
else
{
lean_object* v_k_2331_; lean_object* v_v_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v_k_2331_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_k_2331_);
v_v_2332_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_v_2332_);
lean_dec_ref(v___x_2188_);
v___x_2333_ = lean_unsigned_to_nat(2u);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v_r_2036_);
lean_ctor_set(v___x_2186_, 3, v_l_2022_);
lean_ctor_set(v___x_2186_, 2, v_v_2332_);
lean_ctor_set(v___x_2186_, 1, v_k_2331_);
lean_ctor_set(v___x_2186_, 0, v___x_2333_);
v___x_2335_ = v___x_2186_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2331_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2332_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_l_2022_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_r_2036_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
}
}
else
{
return v_l_2022_;
}
}
else
{
return v_r_2023_;
}
}
else
{
lean_object* v_val_2343_; lean_object* v___x_2345_; 
v_val_2343_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_val_2343_);
lean_dec_ref_known(v___x_2031_, 1);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 2, v_val_2343_);
lean_ctor_set(v___x_2025_, 1, v_k_2017_);
v___x_2345_ = v___x_2025_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_size_2019_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2017_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_val_2343_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_l_2022_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_r_2023_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
default: 
{
lean_object* v_impl_2347_; lean_object* v___x_2348_; 
lean_del_object(v___x_2025_);
lean_dec(v_size_2019_);
v_impl_2347_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2016_, v_k_2017_, v_r_2023_);
v___x_2348_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2020_, v_v_2021_, v_l_2022_, v_impl_2347_);
return v___x_2348_;
}
}
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2016_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_dec(v_k_2017_);
return v_t_2018_;
}
else
{
lean_object* v_val_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_val_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v_k_2017_);
lean_ctor_set(v___x_2354_, 2, v_val_2352_);
lean_ctor_set(v___x_2354_, 3, v_t_2018_);
lean_ctor_set(v___x_2354_, 4, v_t_2018_);
return v___x_2354_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2355_, lean_object* v_i_2356_, lean_object* v_k_2357_){
_start:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = lean_array_get_size(v_keys_2355_);
v___x_2359_ = lean_nat_dec_lt(v_i_2356_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec(v_i_2356_);
return v___x_2359_;
}
else
{
lean_object* v_k_x27_2360_; uint8_t v___x_2361_; 
v_k_x27_2360_ = lean_array_fget_borrowed(v_keys_2355_, v_i_2356_);
v___x_2361_ = lean_name_eq(v_k_2357_, v_k_x27_2360_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = lean_nat_add(v_i_2356_, v___x_2362_);
lean_dec(v_i_2356_);
v_i_2356_ = v___x_2363_;
goto _start;
}
else
{
lean_dec(v_i_2356_);
return v___x_2359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2365_, lean_object* v_i_2366_, lean_object* v_k_2367_){
_start:
{
uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_res_2368_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2365_, v_i_2366_, v_k_2367_);
lean_dec(v_k_2367_);
lean_dec_ref(v_keys_2365_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_2370_, size_t v_x_2371_, lean_object* v_x_2372_){
_start:
{
if (lean_obj_tag(v_x_2370_) == 0)
{
lean_object* v_es_2373_; lean_object* v___x_2374_; size_t v___x_2375_; size_t v___x_2376_; lean_object* v_j_2377_; lean_object* v___x_2378_; 
v_es_2373_ = lean_ctor_get(v_x_2370_, 0);
v___x_2374_ = lean_box(2);
v___x_2375_ = ((size_t)31ULL);
v___x_2376_ = lean_usize_land(v_x_2371_, v___x_2375_);
v_j_2377_ = lean_usize_to_nat(v___x_2376_);
v___x_2378_ = lean_array_get_borrowed(v___x_2374_, v_es_2373_, v_j_2377_);
lean_dec(v_j_2377_);
switch(lean_obj_tag(v___x_2378_))
{
case 0:
{
lean_object* v_key_2379_; uint8_t v___x_2380_; 
v_key_2379_ = lean_ctor_get(v___x_2378_, 0);
v___x_2380_ = lean_name_eq(v_x_2372_, v_key_2379_);
return v___x_2380_;
}
case 1:
{
lean_object* v_node_2381_; size_t v___x_2382_; size_t v___x_2383_; 
v_node_2381_ = lean_ctor_get(v___x_2378_, 0);
v___x_2382_ = ((size_t)5ULL);
v___x_2383_ = lean_usize_shift_right(v_x_2371_, v___x_2382_);
v_x_2370_ = v_node_2381_;
v_x_2371_ = v___x_2383_;
goto _start;
}
default: 
{
uint8_t v___x_2385_; 
v___x_2385_ = 0;
return v___x_2385_;
}
}
}
else
{
lean_object* v_ks_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v_ks_2386_ = lean_ctor_get(v_x_2370_, 0);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_2386_, v___x_2387_, v_x_2372_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
size_t v_x_3826__boxed_2392_; uint8_t v_res_2393_; lean_object* v_r_2394_; 
v_x_3826__boxed_2392_ = lean_unbox_usize(v_x_2390_);
lean_dec(v_x_2390_);
v_res_2393_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2389_, v_x_3826__boxed_2392_, v_x_2391_);
lean_dec(v_x_2391_);
lean_dec_ref(v_x_2389_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint64_t v___y_2398_; 
if (lean_obj_tag(v_x_2396_) == 0)
{
uint64_t v___x_2401_; 
v___x_2401_ = 1723ULL;
v___y_2398_ = v___x_2401_;
goto v___jp_2397_;
}
else
{
uint64_t v_hash_2402_; 
v_hash_2402_ = lean_ctor_get_uint64(v_x_2396_, sizeof(void*)*2);
v___y_2398_ = v_hash_2402_;
goto v___jp_2397_;
}
v___jp_2397_:
{
size_t v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_uint64_to_usize(v___y_2398_);
v___x_2400_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2395_, v___x_2399_, v_x_2396_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_res_2405_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2403_, v_x_2404_);
lean_dec(v_x_2404_);
lean_dec_ref(v_x_2403_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_2407_, lean_object* v_a_2408_, uint8_t v___x_2409_, lean_object* v_x_2410_, lean_object* v_____s_2411_){
_start:
{
lean_object* v_fst_2412_; lean_object* v_kinds_2413_; uint8_t v___x_2414_; 
v_fst_2412_ = lean_ctor_get(v_x_2410_, 0);
lean_inc(v_fst_2412_);
lean_dec_ref(v_x_2410_);
v_kinds_2413_ = lean_ctor_get(v_tactics_2407_, 1);
v___x_2414_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_2413_, v_fst_2412_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_dec(v_fst_2412_);
lean_dec(v_a_2408_);
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_____s_2411_);
return v___x_2415_;
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = l_Lean_Name_toString(v_a_2408_, v___x_2409_);
v___x_2417_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2416_, v_fst_2412_, v_____s_2411_);
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_2419_, lean_object* v_a_2420_, lean_object* v___x_2421_, lean_object* v_x_2422_, lean_object* v_____s_2423_){
_start:
{
uint8_t v___x_3882__boxed_2424_; lean_object* v_res_2425_; 
v___x_3882__boxed_2424_ = lean_unbox(v___x_2421_);
v_res_2425_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2419_, v_a_2420_, v___x_3882__boxed_2424_, v_x_2422_, v_____s_2423_);
lean_dec_ref(v_tactics_2419_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_2426_, lean_object* v_keys_2427_, lean_object* v_vals_2428_, lean_object* v_i_2429_, lean_object* v_acc_2430_){
_start:
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = lean_array_get_size(v_keys_2427_);
v___x_2432_ = lean_nat_dec_lt(v_i_2429_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
lean_dec(v_i_2429_);
lean_dec_ref(v_f_2426_);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_acc_2430_);
return v___x_2433_;
}
else
{
lean_object* v_k_2434_; lean_object* v_v_2435_; lean_object* v___x_2436_; 
v_k_2434_ = lean_array_fget_borrowed(v_keys_2427_, v_i_2429_);
v_v_2435_ = lean_array_fget_borrowed(v_vals_2428_, v_i_2429_);
lean_inc_ref(v_f_2426_);
lean_inc(v_v_2435_);
lean_inc(v_k_2434_);
v___x_2436_ = lean_apply_3(v_f_2426_, v_acc_2430_, v_k_2434_, v_v_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_dec(v_i_2429_);
lean_dec_ref(v_f_2426_);
return v___x_2436_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_nat_add(v_i_2429_, v___x_2438_);
lean_dec(v_i_2429_);
v_i_2429_ = v___x_2439_;
v_acc_2430_ = v_a_2437_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_2441_, lean_object* v_keys_2442_, lean_object* v_vals_2443_, lean_object* v_i_2444_, lean_object* v_acc_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2441_, v_keys_2442_, v_vals_2443_, v_i_2444_, v_acc_2445_);
lean_dec_ref(v_vals_2443_);
lean_dec_ref(v_keys_2442_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_2447_, lean_object* v_as_2448_, size_t v_i_2449_, size_t v_stop_2450_, lean_object* v_b_2451_){
_start:
{
lean_object* v_a_2453_; lean_object* v___y_2458_; uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_eq(v_i_2449_, v_stop_2450_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_array_uget_borrowed(v_as_2448_, v_i_2449_);
switch(lean_obj_tag(v___x_2461_))
{
case 0:
{
lean_object* v_key_2462_; lean_object* v_val_2463_; lean_object* v___x_2464_; 
v_key_2462_ = lean_ctor_get(v___x_2461_, 0);
v_val_2463_ = lean_ctor_get(v___x_2461_, 1);
lean_inc_ref(v_f_2447_);
lean_inc(v_val_2463_);
lean_inc(v_key_2462_);
v___x_2464_ = lean_apply_3(v_f_2447_, v_b_2451_, v_key_2462_, v_val_2463_);
v___y_2458_ = v___x_2464_;
goto v___jp_2457_;
}
case 1:
{
lean_object* v_node_2465_; lean_object* v___x_2466_; 
v_node_2465_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_node_2465_);
lean_inc_ref(v_f_2447_);
v___x_2466_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2447_, v_node_2465_, v_b_2451_);
v___y_2458_ = v___x_2466_;
goto v___jp_2457_;
}
default: 
{
v_a_2453_ = v_b_2451_;
goto v___jp_2452_;
}
}
}
else
{
lean_object* v___x_2467_; 
lean_dec_ref(v_f_2447_);
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_b_2451_);
return v___x_2467_;
}
v___jp_2452_:
{
size_t v___x_2454_; size_t v___x_2455_; 
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2449_, v___x_2454_);
v_i_2449_ = v___x_2455_;
v_b_2451_ = v_a_2453_;
goto _start;
}
v___jp_2457_:
{
if (lean_obj_tag(v___y_2458_) == 0)
{
lean_dec_ref(v_f_2447_);
return v___y_2458_;
}
else
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v___y_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___y_2458_, 1);
v_a_2453_ = v_a_2459_;
goto v___jp_2452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2469_) == 0)
{
lean_object* v_es_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2484_; 
v_es_2471_ = lean_ctor_get(v_x_2469_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_x_2469_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2473_ = v_x_2469_;
v_isShared_2474_ = v_isSharedCheck_2484_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_es_2471_);
lean_dec(v_x_2469_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2484_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = lean_array_get_size(v_es_2471_);
v___x_2477_ = lean_nat_dec_lt(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2479_; 
lean_dec_ref(v_es_2471_);
lean_dec_ref(v_f_2468_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set_tag(v___x_2473_, 1);
lean_ctor_set(v___x_2473_, 0, v_x_2470_);
v___x_2479_ = v___x_2473_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_x_2470_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
lean_del_object(v___x_2473_);
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2476_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2468_, v_es_2471_, v___x_2481_, v___x_2482_, v_x_2470_);
lean_dec_ref(v_es_2471_);
return v___x_2483_;
}
}
}
else
{
lean_object* v_ks_2485_; lean_object* v_vs_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v_ks_2485_ = lean_ctor_get(v_x_2469_, 0);
lean_inc_ref(v_ks_2485_);
v_vs_2486_ = lean_ctor_get(v_x_2469_, 1);
lean_inc_ref(v_vs_2486_);
lean_dec_ref_known(v_x_2469_, 2);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2468_, v_ks_2485_, v_vs_2486_, v___x_2487_, v_x_2470_);
lean_dec_ref(v_vs_2486_);
lean_dec_ref(v_ks_2485_);
return v___x_2488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_2489_, lean_object* v_as_2490_, lean_object* v_i_2491_, lean_object* v_stop_2492_, lean_object* v_b_2493_){
_start:
{
size_t v_i_boxed_2494_; size_t v_stop_boxed_2495_; lean_object* v_res_2496_; 
v_i_boxed_2494_ = lean_unbox_usize(v_i_2491_);
lean_dec(v_i_2491_);
v_stop_boxed_2495_ = lean_unbox_usize(v_stop_2492_);
lean_dec(v_stop_2492_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2489_, v_as_2490_, v_i_boxed_2494_, v_stop_boxed_2495_, v_b_2493_);
lean_dec_ref(v_as_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_2497_, lean_object* v_s_2498_, lean_object* v_a_2499_, lean_object* v_b_2500_){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2499_);
lean_ctor_set(v___x_2501_, 1, v_b_2500_);
v___x_2502_ = lean_apply_2(v_f_2497_, v___x_2501_, v_s_2498_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2502_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
v_a_2511_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2502_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2502_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_2519_, lean_object* v_init_2520_, lean_object* v_f_2521_){
_start:
{
lean_object* v___f_2522_; lean_object* v___x_2523_; lean_object* v_a_2524_; 
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2522_, 0, v_f_2521_);
lean_inc_ref(v_map_2519_);
v___x_2523_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_2522_, v_map_2519_, v_init_2520_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2523_);
return v_a_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_2525_, lean_object* v_init_2526_, lean_object* v_f_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2525_, v_init_2526_, v_f_2527_);
lean_dec_ref(v_map_2525_);
return v_res_2528_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_2531_, lean_object* v_a_2532_, uint8_t v___x_2533_, lean_object* v_as_x27_2534_, lean_object* v_b_2535_){
_start:
{
if (lean_obj_tag(v_as_x27_2534_) == 0)
{
lean_dec(v_a_2532_);
lean_dec_ref(v_tactics_2531_);
return v_b_2535_;
}
else
{
lean_object* v_head_2536_; lean_object* v_fst_2537_; lean_object* v_info_2538_; lean_object* v_tail_2539_; lean_object* v_collectKinds_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v_head_2536_ = lean_ctor_get(v_as_x27_2534_, 0);
v_fst_2537_ = lean_ctor_get(v_head_2536_, 0);
v_info_2538_ = lean_ctor_get(v_fst_2537_, 0);
v_tail_2539_ = lean_ctor_get(v_as_x27_2534_, 1);
v_collectKinds_2540_ = lean_ctor_get(v_info_2538_, 1);
v___x_2541_ = lean_box(v___x_2533_);
lean_inc(v_a_2532_);
lean_inc_ref(v_tactics_2531_);
v___f_2542_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2542_, 0, v_tactics_2531_);
lean_closure_set(v___f_2542_, 1, v_a_2532_);
lean_closure_set(v___f_2542_, 2, v___x_2541_);
v___x_2543_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_2540_);
v___x_2544_ = lean_apply_1(v_collectKinds_2540_, v___x_2543_);
v___x_2545_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_2544_, v_b_2535_, v___f_2542_);
lean_dec_ref(v___x_2544_);
v_as_x27_2534_ = v_tail_2539_;
v_b_2535_ = v___x_2545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_2547_, lean_object* v_a_2548_, lean_object* v___x_2549_, lean_object* v_as_x27_2550_, lean_object* v_b_2551_){
_start:
{
uint8_t v___x_4041__boxed_2552_; lean_object* v_res_2553_; 
v___x_4041__boxed_2552_ = lean_unbox(v___x_2549_);
v_res_2553_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2547_, v_a_2548_, v___x_4041__boxed_2552_, v_as_x27_2550_, v_b_2551_);
lean_dec(v_as_x27_2550_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_2556_, lean_object* v_init_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 0)
{
lean_object* v_k_2559_; lean_object* v_v_2560_; lean_object* v_l_2561_; lean_object* v_r_2562_; lean_object* v___x_2563_; lean_object* v_a_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_k_2559_ = lean_ctor_get(v_x_2558_, 1);
lean_inc(v_k_2559_);
v_v_2560_ = lean_ctor_get(v_x_2558_, 2);
lean_inc(v_v_2560_);
v_l_2561_ = lean_ctor_get(v_x_2558_, 3);
lean_inc(v_l_2561_);
v_r_2562_ = lean_ctor_get(v_x_2558_, 4);
lean_inc(v_r_2562_);
lean_dec_ref_known(v_x_2558_, 5);
lean_inc_ref(v_tactics_2556_);
v___x_2563_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2556_, v_init_2557_, v_l_2561_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref(v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0));
v___x_2566_ = lean_name_eq(v_k_2559_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
lean_inc_ref(v_tactics_2556_);
v___x_2567_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2556_, v_k_2559_, v___x_2566_, v_v_2560_, v_a_2564_);
lean_dec(v_v_2560_);
v_init_2557_ = v___x_2567_;
v_x_2558_ = v_r_2562_;
goto _start;
}
else
{
lean_dec(v_v_2560_);
lean_dec(v_k_2559_);
v_init_2557_ = v_a_2564_;
v_x_2558_ = v_r_2562_;
goto _start;
}
}
else
{
lean_object* v___x_2570_; 
lean_dec_ref(v_tactics_2556_);
v___x_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_init_2557_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_2571_, lean_object* v_table_2572_, lean_object* v_firsts_2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v_a_2575_; 
v___x_2574_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2571_, v_firsts_2573_, v_table_2572_);
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2574_);
return v_a_2575_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2577_, v_x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_){
_start:
{
uint8_t v_res_2583_; lean_object* v_r_2584_; 
v_res_2583_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_2580_, v_x_2581_, v_x_2582_);
lean_dec(v_x_2582_);
lean_dec_ref(v_x_2581_);
v_r_2584_ = lean_box(v_res_2583_);
return v_r_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_2585_, lean_object* v_k_2586_, lean_object* v_t_2587_, lean_object* v_hl_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2585_, v_k_2586_, v_t_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_map_2592_, lean_object* v_init_2593_, lean_object* v_f_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2592_, v_init_2593_, v_f_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_map_2598_, lean_object* v_init_2599_, lean_object* v_f_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_2596_, v_00_u03b2_2597_, v_map_2598_, v_init_2599_, v_f_2600_);
lean_dec_ref(v_map_2598_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_2602_, lean_object* v_a_2603_, uint8_t v___x_2604_, lean_object* v_as_2605_, lean_object* v_as_x27_2606_, lean_object* v_b_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2602_, v_a_2603_, v___x_2604_, v_as_x27_2606_, v_b_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_2610_, lean_object* v_a_2611_, lean_object* v___x_2612_, lean_object* v_as_2613_, lean_object* v_as_x27_2614_, lean_object* v_b_2615_, lean_object* v_a_2616_){
_start:
{
uint8_t v___x_4118__boxed_2617_; lean_object* v_res_2618_; 
v___x_4118__boxed_2617_ = lean_unbox(v___x_2612_);
v_res_2618_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2610_, v_a_2611_, v___x_4118__boxed_2617_, v_as_2613_, v_as_x27_2614_, v_b_2615_, v_a_2616_);
lean_dec(v_as_x27_2614_);
lean_dec(v_as_2613_);
return v_res_2618_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_2619_, lean_object* v_x_2620_, size_t v_x_2621_, lean_object* v_x_2622_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2620_, v_x_2621_, v_x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_){
_start:
{
size_t v_x_4127__boxed_2628_; uint8_t v_res_2629_; lean_object* v_r_2630_; 
v_x_4127__boxed_2628_ = lean_unbox_usize(v_x_2626_);
lean_dec(v_x_2626_);
v_res_2629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_2624_, v_x_2625_, v_x_4127__boxed_2628_, v_x_2627_);
lean_dec(v_x_2627_);
lean_dec_ref(v_x_2625_);
v_r_2630_ = lean_box(v_res_2629_);
return v_r_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_2631_, lean_object* v_f_2632_, lean_object* v_init_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2632_, v_map_2631_, v_init_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_2635_, lean_object* v_00_u03c3_2636_, lean_object* v_00_u03b2_2637_, lean_object* v_map_2638_, lean_object* v_f_2639_, lean_object* v_init_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2639_, v_map_2638_, v_init_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2642_, lean_object* v_keys_2643_, lean_object* v_vals_2644_, lean_object* v_heq_2645_, lean_object* v_i_2646_, lean_object* v_k_2647_){
_start:
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2643_, v_i_2646_, v_k_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2649_, lean_object* v_keys_2650_, lean_object* v_vals_2651_, lean_object* v_heq_2652_, lean_object* v_i_2653_, lean_object* v_k_2654_){
_start:
{
uint8_t v_res_2655_; lean_object* v_r_2656_; 
v_res_2655_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_2649_, v_keys_2650_, v_vals_2651_, v_heq_2652_, v_i_2653_, v_k_2654_);
lean_dec(v_k_2654_);
lean_dec_ref(v_vals_2651_);
lean_dec_ref(v_keys_2650_);
v_r_2656_ = lean_box(v_res_2655_);
return v_r_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_2657_, lean_object* v_00_u03c3_2658_, lean_object* v_00_u03b1_2659_, lean_object* v_00_u03b2_2660_, lean_object* v_f_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2661_, v_x_2662_, v_x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_2665_, lean_object* v_00_u03b2_2666_, lean_object* v_00_u03c3_2667_, lean_object* v_00_u03c3_2668_, lean_object* v_f_2669_, lean_object* v_as_2670_, size_t v_i_2671_, size_t v_stop_2672_, lean_object* v_b_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2669_, v_as_2670_, v_i_2671_, v_stop_2672_, v_b_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_00_u03b2_2676_, lean_object* v_00_u03c3_2677_, lean_object* v_00_u03c3_2678_, lean_object* v_f_2679_, lean_object* v_as_2680_, lean_object* v_i_2681_, lean_object* v_stop_2682_, lean_object* v_b_2683_){
_start:
{
size_t v_i_boxed_2684_; size_t v_stop_boxed_2685_; lean_object* v_res_2686_; 
v_i_boxed_2684_ = lean_unbox_usize(v_i_2681_);
lean_dec(v_i_2681_);
v_stop_boxed_2685_ = lean_unbox_usize(v_stop_2682_);
lean_dec(v_stop_2682_);
v_res_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_2675_, v_00_u03b2_2676_, v_00_u03c3_2677_, v_00_u03c3_2678_, v_f_2679_, v_as_2680_, v_i_boxed_2684_, v_stop_boxed_2685_, v_b_2683_);
lean_dec_ref(v_as_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_2687_, lean_object* v_00_u03c3_2688_, lean_object* v_00_u03b1_2689_, lean_object* v_00_u03b2_2690_, lean_object* v_f_2691_, lean_object* v_keys_2692_, lean_object* v_vals_2693_, lean_object* v_heq_2694_, lean_object* v_i_2695_, lean_object* v_acc_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2691_, v_keys_2692_, v_vals_2693_, v_i_2695_, v_acc_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_2698_, lean_object* v_00_u03c3_2699_, lean_object* v_00_u03b1_2700_, lean_object* v_00_u03b2_2701_, lean_object* v_f_2702_, lean_object* v_keys_2703_, lean_object* v_vals_2704_, lean_object* v_heq_2705_, lean_object* v_i_2706_, lean_object* v_acc_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_2698_, v_00_u03c3_2699_, v_00_u03b1_2700_, v_00_u03b2_2701_, v_f_2702_, v_keys_2703_, v_vals_2704_, v_heq_2705_, v_i_2706_, v_acc_2707_);
lean_dec_ref(v_vals_2704_);
lean_dec_ref(v_keys_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_2709_, lean_object* v_x2_2710_){
_start:
{
lean_object* v_fst_2711_; lean_object* v_snd_2712_; lean_object* v___x_2713_; 
v_fst_2711_ = lean_ctor_get(v_x2_2710_, 0);
lean_inc(v_fst_2711_);
v_snd_2712_ = lean_ctor_get(v_x2_2710_, 1);
lean_inc(v_snd_2712_);
lean_dec_ref(v_x2_2710_);
v___x_2713_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2711_, v_snd_2712_, v_x1_2709_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_2733_, lean_object* v_x1_2734_, lean_object* v_x2_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = lean_array_get_size(v_x2_2735_);
v___x_2738_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2739_ = lean_nat_dec_lt(v___x_2736_, v___x_2737_);
if (v___x_2739_ == 0)
{
lean_dec_ref(v_x2_2735_);
lean_dec_ref(v___f_2733_);
return v_x1_2734_;
}
else
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = lean_usize_of_nat(v___x_2737_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2738_, v___f_2733_, v_x2_2735_, v___x_2740_, v___x_2741_, v_x1_2734_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_2746_, lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v___x_2749_, lean_object* v___x_2750_, lean_object* v_toPure_2751_, lean_object* v___f_2752_, lean_object* v_env_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v_ext_2755_; lean_object* v_toEnvExtension_2756_; lean_object* v_asyncMode_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; lean_object* v_categories_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2754_ = l_Lean_Parser_parserExtension;
v_ext_2755_ = lean_ctor_get(v___x_2754_, 1);
v_toEnvExtension_2756_ = lean_ctor_get(v_ext_2755_, 0);
v_asyncMode_2757_ = lean_ctor_get(v_toEnvExtension_2756_, 2);
v___x_2758_ = 0;
lean_inc_ref(v_env_2753_);
v___x_2759_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2746_, v___x_2754_, v_env_2753_, v_asyncMode_2757_, v___x_2758_);
v_categories_2760_ = lean_ctor_get(v___x_2759_, 2);
lean_inc_ref(v_categories_2760_);
lean_dec(v___x_2759_);
v___x_2761_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2762_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2747_, v___x_2748_, v_categories_2760_, v___x_2761_);
lean_dec_ref(v_categories_2760_);
if (lean_obj_tag(v___x_2762_) == 1)
{
lean_object* v_val_2763_; lean_object* v___y_2765_; lean_object* v___x_2772_; lean_object* v_toEnvExtension_2773_; lean_object* v_exportEntriesFn_2774_; lean_object* v_asyncMode_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v_importedEntries_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v_exported_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_val_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2772_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2773_ = lean_ctor_get(v___x_2772_, 0);
v_exportEntriesFn_2774_ = lean_ctor_get(v___x_2772_, 4);
v_asyncMode_2775_ = lean_ctor_get(v_toEnvExtension_2773_, 2);
v___x_2776_ = lean_box(0);
lean_inc_ref_n(v_env_2753_, 2);
v___x_2777_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2749_, v_toEnvExtension_2773_, v_env_2753_, v_asyncMode_2775_, v___x_2776_, v___x_2758_);
v_importedEntries_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_importedEntries_2778_);
lean_dec(v___x_2777_);
v___x_2779_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2750_, v___x_2772_, v_env_2753_, v_asyncMode_2775_, v___x_2776_, v___x_2758_);
lean_inc_ref(v_exportEntriesFn_2774_);
v___x_2780_ = lean_apply_2(v_exportEntriesFn_2774_, v_env_2753_, v___x_2779_);
v_exported_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_exported_2781_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = lean_box(1);
v___x_2783_ = lean_array_push(v_importedEntries_2778_, v_exported_2781_);
v___x_2784_ = lean_unsigned_to_nat(0u);
v___x_2785_ = lean_array_get_size(v___x_2783_);
v___x_2786_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_2787_ = lean_nat_dec_lt(v___x_2784_, v___x_2785_);
if (v___x_2787_ == 0)
{
lean_dec_ref(v___x_2783_);
lean_dec_ref(v___f_2752_);
v___y_2765_ = v___x_2782_;
goto v___jp_2764_;
}
else
{
size_t v___x_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = ((size_t)0ULL);
v___x_2789_ = lean_usize_of_nat(v___x_2785_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2786_, v___f_2752_, v___x_2783_, v___x_2788_, v___x_2789_, v___x_2782_);
v___y_2765_ = v___x_2790_;
goto v___jp_2764_;
}
v___jp_2764_:
{
lean_object* v_tables_2766_; lean_object* v_leadingTable_2767_; lean_object* v_trailingTable_2768_; lean_object* v_firstTokens_2769_; lean_object* v_firstTokens_2770_; lean_object* v___x_2771_; 
v_tables_2766_ = lean_ctor_get(v_val_2763_, 2);
v_leadingTable_2767_ = lean_ctor_get(v_tables_2766_, 0);
v_trailingTable_2768_ = lean_ctor_get(v_tables_2766_, 2);
lean_inc(v_trailingTable_2768_);
lean_inc(v_leadingTable_2767_);
lean_inc(v_val_2763_);
v_firstTokens_2769_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2763_, v_leadingTable_2767_, v___y_2765_);
v_firstTokens_2770_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2763_, v_trailingTable_2768_, v_firstTokens_2769_);
v___x_2771_ = lean_apply_2(v_toPure_2751_, lean_box(0), v_firstTokens_2770_);
return v___x_2771_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_dec(v___x_2762_);
lean_dec_ref(v_env_2753_);
lean_dec_ref(v___f_2752_);
lean_dec(v___x_2750_);
v___x_2791_ = lean_box(1);
v___x_2792_ = lean_apply_2(v_toPure_2751_, lean_box(0), v___x_2791_);
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v___x_2797_, lean_object* v_toPure_2798_, lean_object* v___f_2799_, lean_object* v_env_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_2793_, v___x_2794_, v___x_2795_, v___x_2796_, v___x_2797_, v_toPure_2798_, v___f_2799_, v_env_2800_);
lean_dec_ref(v___x_2796_);
lean_dec_ref(v___x_2793_);
return v_res_2801_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_box(1);
v___x_2806_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_2809_, lean_object* v_inst_2810_){
_start:
{
lean_object* v_toApplicative_2811_; lean_object* v_toBind_2812_; lean_object* v_getEnv_2813_; lean_object* v_toPure_2814_; lean_object* v___f_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; 
v_toApplicative_2811_ = lean_ctor_get(v_inst_2809_, 0);
lean_inc_ref(v_toApplicative_2811_);
v_toBind_2812_ = lean_ctor_get(v_inst_2809_, 1);
lean_inc(v_toBind_2812_);
lean_dec_ref(v_inst_2809_);
v_getEnv_2813_ = lean_ctor_get(v_inst_2810_, 0);
lean_inc(v_getEnv_2813_);
lean_dec_ref(v_inst_2810_);
v_toPure_2814_ = lean_ctor_get(v_toApplicative_2811_, 1);
lean_inc(v_toPure_2814_);
lean_dec_ref(v_toApplicative_2811_);
v___f_2815_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_2816_ = lean_box(1);
v___x_2817_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2818_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2819_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_2820_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2821_, 0, v___x_2820_);
lean_closure_set(v___f_2821_, 1, v___x_2818_);
lean_closure_set(v___f_2821_, 2, v___x_2819_);
lean_closure_set(v___f_2821_, 3, v___x_2817_);
lean_closure_set(v___f_2821_, 4, v___x_2816_);
lean_closure_set(v___f_2821_, 5, v_toPure_2814_);
lean_closure_set(v___f_2821_, 6, v___f_2815_);
v___x_2822_ = lean_apply_4(v_toBind_2812_, lean_box(0), lean_box(0), v_getEnv_2813_, v___f_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_2824_, v_inst_2825_);
return v___x_2826_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__0);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2829_ = lean_box(1);
v___x_2830_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg___closed__4);
v___x_2831_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_2832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v___x_2830_);
lean_ctor_set(v___x_2832_, 2, v___x_2829_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_2834_, lean_object* v___y_2835_, lean_object* v_toPure_2836_, lean_object* v_firsts_2837_, lean_object* v_____do__lift_2838_){
_start:
{
lean_object* v___y_2840_; lean_object* v_val_2851_; 
if (lean_obj_tag(v_____do__lift_2838_) == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_2834_);
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_2853_, v_firsts_2837_, v_n_2834_);
if (lean_obj_tag(v___x_2854_) == 0)
{
uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = 1;
lean_inc(v_n_2834_);
v___x_2856_ = l_Lean_Name_toString(v_n_2834_, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
v___y_2840_ = v___x_2857_;
goto v___jp_2839_;
}
else
{
lean_object* v_val_2858_; 
v_val_2858_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_val_2858_);
lean_dec_ref_known(v___x_2854_, 1);
v_val_2851_ = v_val_2858_;
goto v___jp_2850_;
}
}
else
{
lean_object* v_val_2859_; 
lean_dec(v_firsts_2837_);
v_val_2859_ = lean_ctor_get(v_____do__lift_2838_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v_____do__lift_2838_, 1);
v_val_2851_ = v_val_2859_;
goto v___jp_2850_;
}
v___jp_2839_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2841_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_2842_ = l_Lean_Expr_const___override(v_n_2834_, v___y_2835_);
v___x_2843_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_2844_ = lean_box(0);
v___x_2845_ = 0;
v___x_2846_ = l_Lean_MessageData_withExprHover(v___y_2840_, v___x_2842_, v___x_2843_, v___x_2844_, v___x_2844_, v___x_2844_, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2841_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v___x_2841_);
v___x_2849_ = lean_apply_2(v_toPure_2836_, lean_box(0), v___x_2848_);
return v___x_2849_;
}
v___jp_2850_:
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_val_2851_);
v___y_2840_ = v___x_2852_;
goto v___jp_2839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_2860_, lean_object* v_toPure_2861_, lean_object* v_firsts_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_toBind_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v___f_2868_, lean_object* v_env_2869_){
_start:
{
lean_object* v___y_2871_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = l_Lean_Environment_constants(v_env_2869_);
lean_inc(v_n_2860_);
v___x_2876_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_2866_, v___x_2867_, v___x_2875_, v_n_2860_);
lean_dec_ref(v___x_2875_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref(v___f_2868_);
v___x_2877_ = lean_box(0);
v___y_2871_ = v___x_2877_;
goto v___jp_2870_;
}
else
{
lean_object* v_val_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_val_2878_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2879_ = l_Lean_ConstantInfo_levelParams(v_val_2878_);
lean_dec(v_val_2878_);
v___x_2880_ = lean_box(0);
v___x_2881_ = l_List_mapTR_loop___redArg(v___f_2868_, v___x_2879_, v___x_2880_);
v___y_2871_ = v___x_2881_;
goto v___jp_2870_;
}
v___jp_2870_:
{
lean_object* v___f_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_inc(v_n_2860_);
v___f_2872_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2872_, 0, v_n_2860_);
lean_closure_set(v___f_2872_, 1, v___y_2871_);
lean_closure_set(v___f_2872_, 2, v_toPure_2861_);
lean_closure_set(v___f_2872_, 3, v_firsts_2862_);
v___x_2873_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_2863_, v_inst_2864_, v_n_2860_);
v___x_2874_ = lean_apply_4(v_toBind_2865_, lean_box(0), lean_box(0), v___x_2873_, v___f_2872_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_firsts_2885_, lean_object* v_n_2886_){
_start:
{
lean_object* v_toApplicative_2887_; lean_object* v_toBind_2888_; lean_object* v_getEnv_2889_; lean_object* v_toPure_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; 
v_toApplicative_2887_ = lean_ctor_get(v_inst_2883_, 0);
v_toBind_2888_ = lean_ctor_get(v_inst_2883_, 1);
lean_inc_n(v_toBind_2888_, 2);
v_getEnv_2889_ = lean_ctor_get(v_inst_2884_, 0);
lean_inc(v_getEnv_2889_);
v_toPure_2890_ = lean_ctor_get(v_toApplicative_2887_, 1);
lean_inc(v_toPure_2890_);
v___f_2891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_2892_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_2893_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_2894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_2894_, 0, v_n_2886_);
lean_closure_set(v___f_2894_, 1, v_toPure_2890_);
lean_closure_set(v___f_2894_, 2, v_firsts_2885_);
lean_closure_set(v___f_2894_, 3, v_inst_2883_);
lean_closure_set(v___f_2894_, 4, v_inst_2884_);
lean_closure_set(v___f_2894_, 5, v_toBind_2888_);
lean_closure_set(v___f_2894_, 6, v___x_2892_);
lean_closure_set(v___f_2894_, 7, v___x_2893_);
lean_closure_set(v___f_2894_, 8, v___f_2891_);
v___x_2895_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v_getEnv_2889_, v___f_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_2896_, lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_firsts_2899_, lean_object* v_n_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_2897_, v_inst_2898_, v_firsts_2899_, v_n_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_2907_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_2911_);
lean_dec_ref(v_s_2911_);
return v_res_2912_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_2913_, lean_object* v_x1_2914_, lean_object* v_x2_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v___x_2916_ = l_Lean_Name_toString(v_x1_2914_, v___x_2913_);
v___x_2917_ = l_Lean_Name_toString(v_x2_2915_, v___x_2913_);
v___x_2918_ = lean_string_dec_lt(v___x_2916_, v___x_2917_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_2919_, lean_object* v_x1_2920_, lean_object* v_x2_2921_){
_start:
{
uint8_t v___x_17004__boxed_2922_; uint8_t v_res_2923_; lean_object* v_r_2924_; 
v___x_17004__boxed_2922_ = lean_unbox(v___x_2919_);
v_res_2923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_17004__boxed_2922_, v_x1_2920_, v_x2_2921_);
v_r_2924_ = lean_box(v_res_2923_);
return v_r_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_2925_, lean_object* v_pivot_2926_, lean_object* v_as_2927_, lean_object* v_i_2928_, lean_object* v_k_2929_){
_start:
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_nat_dec_lt(v_k_2929_, v_hi_2925_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_dec(v_k_2929_);
lean_dec(v_pivot_2926_);
v___x_2931_ = lean_array_fswap(v_as_2927_, v_i_2928_, v_hi_2925_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_i_2928_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
return v___x_2932_;
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2933_ = lean_array_fget_borrowed(v_as_2927_, v_k_2929_);
lean_inc(v___x_2933_);
v___x_2934_ = l_Lean_Name_toString(v___x_2933_, v___x_2930_);
lean_inc(v_pivot_2926_);
v___x_2935_ = l_Lean_Name_toString(v_pivot_2926_, v___x_2930_);
v___x_2936_ = lean_string_dec_lt(v___x_2934_, v___x_2935_);
lean_dec_ref(v___x_2935_);
lean_dec_ref(v___x_2934_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_unsigned_to_nat(1u);
v___x_2938_ = lean_nat_add(v_k_2929_, v___x_2937_);
lean_dec(v_k_2929_);
v_k_2929_ = v___x_2938_;
goto _start;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = lean_array_fswap(v_as_2927_, v_i_2928_, v_k_2929_);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_nat_add(v_i_2928_, v___x_2941_);
lean_dec(v_i_2928_);
v___x_2943_ = lean_nat_add(v_k_2929_, v___x_2941_);
lean_dec(v_k_2929_);
v_as_2927_ = v___x_2940_;
v_i_2928_ = v___x_2942_;
v_k_2929_ = v___x_2943_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_2945_, lean_object* v_pivot_2946_, lean_object* v_as_2947_, lean_object* v_i_2948_, lean_object* v_k_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2945_, v_pivot_2946_, v_as_2947_, v_i_2948_, v_k_2949_);
lean_dec(v_hi_2945_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_2951_, lean_object* v_as_2952_, lean_object* v_lo_2953_, lean_object* v_hi_2954_){
_start:
{
lean_object* v___y_2956_; uint8_t v___x_2966_; 
v___x_2966_ = lean_nat_dec_lt(v_lo_2953_, v_hi_2954_);
if (v___x_2966_ == 0)
{
lean_dec(v_lo_2953_);
return v_as_2952_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_mid_2969_; lean_object* v___y_2971_; lean_object* v___y_2977_; lean_object* v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2967_ = lean_nat_add(v_lo_2953_, v_hi_2954_);
v___x_2968_ = lean_unsigned_to_nat(1u);
v_mid_2969_ = lean_nat_shiftr(v___x_2967_, v___x_2968_);
lean_dec(v___x_2967_);
v___x_2982_ = lean_array_fget_borrowed(v_as_2952_, v_mid_2969_);
v___x_2983_ = lean_array_fget_borrowed(v_as_2952_, v_lo_2953_);
lean_inc(v___x_2983_);
lean_inc(v___x_2982_);
v___x_2984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2966_, v___x_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
v___y_2977_ = v_as_2952_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_array_fswap(v_as_2952_, v_lo_2953_, v_mid_2969_);
v___y_2977_ = v___x_2985_;
goto v___jp_2976_;
}
v___jp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_array_fget_borrowed(v___y_2971_, v_mid_2969_);
v___x_2973_ = lean_array_fget_borrowed(v___y_2971_, v_hi_2954_);
lean_inc(v___x_2973_);
lean_inc(v___x_2972_);
v___x_2974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2966_, v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v_mid_2969_);
v___y_2956_ = v___y_2971_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_array_fswap(v___y_2971_, v_mid_2969_, v_hi_2954_);
lean_dec(v_mid_2969_);
v___y_2956_ = v___x_2975_;
goto v___jp_2955_;
}
}
v___jp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_array_fget_borrowed(v___y_2977_, v_hi_2954_);
v___x_2979_ = lean_array_fget_borrowed(v___y_2977_, v_lo_2953_);
lean_inc(v___x_2979_);
lean_inc(v___x_2978_);
v___x_2980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_2966_, v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
v___y_2971_ = v___y_2977_;
goto v___jp_2970_;
}
else
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_array_fswap(v___y_2977_, v_lo_2953_, v_hi_2954_);
v___y_2971_ = v___x_2981_;
goto v___jp_2970_;
}
}
}
v___jp_2955_:
{
lean_object* v_pivot_2957_; lean_object* v___x_2958_; lean_object* v_fst_2959_; lean_object* v_snd_2960_; uint8_t v___x_2961_; 
v_pivot_2957_ = lean_array_fget(v___y_2956_, v_hi_2954_);
lean_inc_n(v_lo_2953_, 2);
v___x_2958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2954_, v_pivot_2957_, v___y_2956_, v_lo_2953_, v_lo_2953_);
v_fst_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_fst_2959_);
v_snd_2960_ = lean_ctor_get(v___x_2958_, 1);
lean_inc(v_snd_2960_);
lean_dec_ref(v___x_2958_);
v___x_2961_ = lean_nat_dec_le(v_hi_2954_, v_fst_2959_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2951_, v_snd_2960_, v_lo_2953_, v_fst_2959_);
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = lean_nat_add(v_fst_2959_, v___x_2963_);
lean_dec(v_fst_2959_);
v_as_2952_ = v___x_2962_;
v_lo_2953_ = v___x_2964_;
goto _start;
}
else
{
lean_dec(v_fst_2959_);
lean_dec(v_lo_2953_);
return v_snd_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_2986_, lean_object* v_as_2987_, lean_object* v_lo_2988_, lean_object* v_hi_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2986_, v_as_2987_, v_lo_2988_, v_hi_2989_);
lean_dec(v_hi_2989_);
lean_dec(v_n_2986_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_2991_, lean_object* v_x_2992_){
_start:
{
if (lean_obj_tag(v_x_2992_) == 0)
{
lean_object* v_k_2993_; lean_object* v_l_2994_; lean_object* v_r_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_k_2993_ = lean_ctor_get(v_x_2992_, 1);
lean_inc(v_k_2993_);
v_l_2994_ = lean_ctor_get(v_x_2992_, 3);
lean_inc(v_l_2994_);
v_r_2995_ = lean_ctor_get(v_x_2992_, 4);
lean_inc(v_r_2995_);
lean_dec_ref_known(v_x_2992_, 5);
v___x_2996_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2991_, v_l_2994_);
v___x_2997_ = lean_array_push(v___x_2996_, v_k_2993_);
v_init_2991_ = v___x_2997_;
v_x_2992_ = v_r_2995_;
goto _start;
}
else
{
return v_init_2991_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
if (lean_obj_tag(v_a_2999_) == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = l_List_reverse___redArg(v_a_3000_);
return v___x_3001_;
}
else
{
lean_object* v_head_3002_; lean_object* v_tail_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3012_; 
v_head_3002_ = lean_ctor_get(v_a_2999_, 0);
v_tail_3003_ = lean_ctor_get(v_a_2999_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3005_ = v_a_2999_;
v_isShared_3006_ = v_isSharedCheck_3012_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_tail_3003_);
lean_inc(v_head_3002_);
lean_dec(v_a_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3012_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = l_Lean_Level_param___override(v_head_3002_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 1, v_a_3000_);
lean_ctor_set(v___x_3005_, 0, v___x_3007_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_a_3000_);
v___x_3009_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v_a_2999_ = v_tail_3003_;
v_a_3000_ = v___x_3009_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_3013_, lean_object* v_x2_3014_){
_start:
{
lean_object* v_fst_3015_; lean_object* v_fst_3016_; uint8_t v___x_3017_; 
v_fst_3015_ = lean_ctor_get(v_x1_3013_, 0);
v_fst_3016_ = lean_ctor_get(v_x2_3014_, 0);
v___x_3017_ = l_Lean_Name_quickLt(v_fst_3015_, v_fst_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_3018_, lean_object* v_x2_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_3018_, v_x2_3019_);
lean_dec_ref(v_x2_3019_);
lean_dec_ref(v_x1_3018_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_3022_, lean_object* v_k_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v_m_3028_; lean_object* v_a_3029_; uint8_t v___x_3030_; 
v___x_3026_ = lean_nat_add(v_x_3024_, v_x_3025_);
v___x_3027_ = lean_unsigned_to_nat(1u);
v_m_3028_ = lean_nat_shiftr(v___x_3026_, v___x_3027_);
lean_dec(v___x_3026_);
v_a_3029_ = lean_array_fget_borrowed(v_as_3022_, v_m_3028_);
v___x_3030_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_3029_, v_k_3023_);
if (v___x_3030_ == 0)
{
uint8_t v___x_3031_; 
lean_dec(v_x_3025_);
v___x_3031_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_3023_, v_a_3029_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec(v_m_3028_);
lean_dec(v_x_3024_);
lean_inc(v_a_3029_);
v___x_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_a_3029_);
return v___x_3032_;
}
else
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = lean_nat_dec_eq(v_m_3028_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = lean_nat_sub(v_m_3028_, v___x_3027_);
lean_dec(v_m_3028_);
v___x_3036_ = lean_nat_dec_lt(v___x_3035_, v_x_3024_);
if (v___x_3036_ == 0)
{
v_x_3025_ = v___x_3035_;
goto _start;
}
else
{
lean_object* v___x_3038_; 
lean_dec(v___x_3035_);
lean_dec(v_x_3024_);
v___x_3038_ = lean_box(0);
return v___x_3038_;
}
}
else
{
lean_object* v___x_3039_; 
lean_dec(v_m_3028_);
lean_dec(v_x_3024_);
v___x_3039_ = lean_box(0);
return v___x_3039_;
}
}
}
else
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
lean_dec(v_x_3024_);
v___x_3040_ = lean_nat_add(v_m_3028_, v___x_3027_);
lean_dec(v_m_3028_);
v___x_3041_ = lean_nat_dec_le(v___x_3040_, v_x_3025_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
lean_dec(v___x_3040_);
lean_dec(v_x_3025_);
v___x_3042_ = lean_box(0);
return v___x_3042_;
}
else
{
v_x_3024_ = v___x_3040_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_3044_, lean_object* v_k_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3044_, v_k_3045_, v_x_3046_, v_x_3047_);
lean_dec_ref(v_k_3045_);
lean_dec_ref(v_as_3044_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_env_3057_; lean_object* v___x_3058_; 
v___x_3052_ = lean_box(1);
v___x_3053_ = lean_st_ref_get(v___y_3050_);
v_env_3057_ = lean_ctor_get(v___x_3053_, 0);
lean_inc_ref(v_env_3057_);
lean_dec(v___x_3053_);
v___x_3058_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3057_, v_tac_3049_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; lean_object* v_toEnvExtension_3060_; lean_object* v_asyncMode_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3059_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3060_ = lean_ctor_get(v___x_3059_, 0);
v_asyncMode_3061_ = lean_ctor_get(v_toEnvExtension_3060_, 2);
v___x_3062_ = lean_box(0);
v___x_3063_ = 0;
v___x_3064_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3052_, v___x_3059_, v_env_3057_, v_asyncMode_3061_, v___x_3062_, v___x_3063_);
v___x_3065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3064_, v_tac_3049_);
lean_dec(v_tac_3049_);
lean_dec(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
else
{
lean_object* v_val_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3095_; 
v_val_3067_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3069_ = v___x_3058_;
v_isShared_3070_ = v_isSharedCheck_3095_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_val_3067_);
lean_dec(v___x_3058_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3095_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3071_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3072_ = 0;
v___x_3073_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3052_, v___x_3071_, v_env_3057_, v_val_3067_, v___x_3072_);
lean_dec(v_val_3067_);
lean_dec_ref(v_env_3057_);
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_array_get_size(v___x_3073_);
v___x_3076_ = lean_nat_dec_lt(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_dec_ref(v___x_3073_);
lean_del_object(v___x_3069_);
lean_dec(v_tac_3049_);
goto v___jp_3054_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3078_ = lean_nat_sub(v___x_3075_, v___x_3077_);
v___x_3079_ = lean_nat_dec_le(v___x_3074_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_dec(v___x_3078_);
lean_dec_ref(v___x_3073_);
lean_del_object(v___x_3069_);
lean_dec(v_tac_3049_);
goto v___jp_3054_;
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_tac_3049_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_3073_, v___x_3081_, v___x_3074_, v___x_3078_);
lean_dec_ref_known(v___x_3081_, 2);
lean_dec_ref(v___x_3073_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_del_object(v___x_3069_);
goto v___jp_3054_;
}
else
{
lean_object* v_val_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3094_; 
v_val_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_val_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v_snd_3087_; lean_object* v___x_3089_; 
v_snd_3087_ = lean_ctor_get(v_val_3083_, 1);
lean_inc(v_snd_3087_);
lean_dec(v_val_3083_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_snd_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_snd_3087_);
v___x_3089_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3091_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3089_);
v___x_3091_ = v___x_3069_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
}
}
v___jp_3054_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3096_, v___y_3097_);
lean_dec(v___y_3097_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_3100_, lean_object* v_k_3101_){
_start:
{
if (lean_obj_tag(v_t_3100_) == 0)
{
lean_object* v_k_3102_; lean_object* v_v_3103_; lean_object* v_l_3104_; lean_object* v_r_3105_; uint8_t v___x_3106_; 
v_k_3102_ = lean_ctor_get(v_t_3100_, 1);
v_v_3103_ = lean_ctor_get(v_t_3100_, 2);
v_l_3104_ = lean_ctor_get(v_t_3100_, 3);
v_r_3105_ = lean_ctor_get(v_t_3100_, 4);
v___x_3106_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3101_, v_k_3102_);
switch(v___x_3106_)
{
case 0:
{
v_t_3100_ = v_l_3104_;
goto _start;
}
case 1:
{
lean_object* v___x_3108_; 
lean_inc(v_v_3103_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_v_3103_);
return v___x_3108_;
}
default: 
{
v_t_3100_ = v_r_3105_;
goto _start;
}
}
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_box(0);
return v___x_3110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_3111_, lean_object* v_k_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3111_, v_k_3112_);
lean_dec(v_k_3112_);
lean_dec(v_t_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_3114_, lean_object* v_x_3115_){
_start:
{
if (lean_obj_tag(v_x_3115_) == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
else
{
lean_object* v_key_3117_; lean_object* v_value_3118_; lean_object* v_tail_3119_; uint8_t v___x_3120_; 
v_key_3117_ = lean_ctor_get(v_x_3115_, 0);
v_value_3118_ = lean_ctor_get(v_x_3115_, 1);
v_tail_3119_ = lean_ctor_get(v_x_3115_, 2);
v___x_3120_ = lean_name_eq(v_key_3117_, v_a_3114_);
if (v___x_3120_ == 0)
{
v_x_3115_ = v_tail_3119_;
goto _start;
}
else
{
lean_object* v___x_3122_; 
lean_inc(v_value_3118_);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_value_3118_);
return v___x_3122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3123_, v_x_3124_);
lean_dec(v_x_3124_);
lean_dec(v_a_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v_buckets_3128_; lean_object* v___x_3129_; uint64_t v___y_3131_; 
v_buckets_3128_ = lean_ctor_get(v_m_3126_, 1);
v___x_3129_ = lean_array_get_size(v_buckets_3128_);
if (lean_obj_tag(v_a_3127_) == 0)
{
uint64_t v___x_3145_; 
v___x_3145_ = 1723ULL;
v___y_3131_ = v___x_3145_;
goto v___jp_3130_;
}
else
{
uint64_t v_hash_3146_; 
v_hash_3146_ = lean_ctor_get_uint64(v_a_3127_, sizeof(void*)*2);
v___y_3131_ = v_hash_3146_;
goto v___jp_3130_;
}
v___jp_3130_:
{
uint64_t v___x_3132_; uint64_t v___x_3133_; uint64_t v_fold_3134_; uint64_t v___x_3135_; uint64_t v___x_3136_; uint64_t v___x_3137_; size_t v___x_3138_; size_t v___x_3139_; size_t v___x_3140_; size_t v___x_3141_; size_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3132_ = 32ULL;
v___x_3133_ = lean_uint64_shift_right(v___y_3131_, v___x_3132_);
v_fold_3134_ = lean_uint64_xor(v___y_3131_, v___x_3133_);
v___x_3135_ = 16ULL;
v___x_3136_ = lean_uint64_shift_right(v_fold_3134_, v___x_3135_);
v___x_3137_ = lean_uint64_xor(v_fold_3134_, v___x_3136_);
v___x_3138_ = lean_uint64_to_usize(v___x_3137_);
v___x_3139_ = lean_usize_of_nat(v___x_3129_);
v___x_3140_ = ((size_t)1ULL);
v___x_3141_ = lean_usize_sub(v___x_3139_, v___x_3140_);
v___x_3142_ = lean_usize_land(v___x_3138_, v___x_3141_);
v___x_3143_ = lean_array_uget_borrowed(v_buckets_3128_, v___x_3142_);
v___x_3144_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3127_, v___x_3143_);
return v___x_3144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_m_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_3150_, lean_object* v_vals_3151_, lean_object* v_i_3152_, lean_object* v_k_3153_){
_start:
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = lean_array_get_size(v_keys_3150_);
v___x_3155_ = lean_nat_dec_lt(v_i_3152_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec(v_i_3152_);
v___x_3156_ = lean_box(0);
return v___x_3156_;
}
else
{
lean_object* v_k_x27_3157_; uint8_t v___x_3158_; 
v_k_x27_3157_ = lean_array_fget_borrowed(v_keys_3150_, v_i_3152_);
v___x_3158_ = lean_name_eq(v_k_3153_, v_k_x27_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_nat_add(v_i_3152_, v___x_3159_);
lean_dec(v_i_3152_);
v_i_3152_ = v___x_3160_;
goto _start;
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_array_fget_borrowed(v_vals_3151_, v_i_3152_);
lean_dec(v_i_3152_);
lean_inc(v___x_3162_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_3164_, lean_object* v_vals_3165_, lean_object* v_i_3166_, lean_object* v_k_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3164_, v_vals_3165_, v_i_3166_, v_k_3167_);
lean_dec(v_k_3167_);
lean_dec_ref(v_vals_3165_);
lean_dec_ref(v_keys_3164_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3169_, size_t v_x_3170_, lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3169_) == 0)
{
lean_object* v_es_3172_; lean_object* v___x_3173_; size_t v___x_3174_; size_t v___x_3175_; lean_object* v_j_3176_; lean_object* v___x_3177_; 
v_es_3172_ = lean_ctor_get(v_x_3169_, 0);
v___x_3173_ = lean_box(2);
v___x_3174_ = ((size_t)31ULL);
v___x_3175_ = lean_usize_land(v_x_3170_, v___x_3174_);
v_j_3176_ = lean_usize_to_nat(v___x_3175_);
v___x_3177_ = lean_array_get_borrowed(v___x_3173_, v_es_3172_, v_j_3176_);
lean_dec(v_j_3176_);
switch(lean_obj_tag(v___x_3177_))
{
case 0:
{
lean_object* v_key_3178_; lean_object* v_val_3179_; uint8_t v___x_3180_; 
v_key_3178_ = lean_ctor_get(v___x_3177_, 0);
v_val_3179_ = lean_ctor_get(v___x_3177_, 1);
v___x_3180_ = lean_name_eq(v_x_3171_, v_key_3178_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_box(0);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; 
lean_inc(v_val_3179_);
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_val_3179_);
return v___x_3182_;
}
}
case 1:
{
lean_object* v_node_3183_; size_t v___x_3184_; size_t v___x_3185_; 
v_node_3183_ = lean_ctor_get(v___x_3177_, 0);
v___x_3184_ = ((size_t)5ULL);
v___x_3185_ = lean_usize_shift_right(v_x_3170_, v___x_3184_);
v_x_3169_ = v_node_3183_;
v_x_3170_ = v___x_3185_;
goto _start;
}
default: 
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_box(0);
return v___x_3187_;
}
}
}
else
{
lean_object* v_ks_3188_; lean_object* v_vs_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v_ks_3188_ = lean_ctor_get(v_x_3169_, 0);
v_vs_3189_ = lean_ctor_get(v_x_3169_, 1);
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_3188_, v_vs_3189_, v___x_3190_, v_x_3171_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_3192_, lean_object* v_x_3193_, lean_object* v_x_3194_){
_start:
{
size_t v_x_17377__boxed_3195_; lean_object* v_res_3196_; 
v_x_17377__boxed_3195_ = lean_unbox_usize(v_x_3193_);
lean_dec(v_x_3193_);
v_res_3196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3192_, v_x_17377__boxed_3195_, v_x_3194_);
lean_dec(v_x_3194_);
lean_dec_ref(v_x_3192_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
uint64_t v___y_3200_; 
if (lean_obj_tag(v_x_3198_) == 0)
{
uint64_t v___x_3203_; 
v___x_3203_ = 1723ULL;
v___y_3200_ = v___x_3203_;
goto v___jp_3199_;
}
else
{
uint64_t v_hash_3204_; 
v_hash_3204_ = lean_ctor_get_uint64(v_x_3198_, sizeof(void*)*2);
v___y_3200_ = v_hash_3204_;
goto v___jp_3199_;
}
v___jp_3199_:
{
size_t v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = lean_uint64_to_usize(v___y_3200_);
v___x_3202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3197_, v___x_3201_, v_x_3198_);
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3205_, v_x_3206_);
lean_dec(v_x_3206_);
lean_dec_ref(v_x_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_3208_, lean_object* v_x_3209_){
_start:
{
uint8_t v_stage_u2081_3210_; 
v_stage_u2081_3210_ = lean_ctor_get_uint8(v_x_3208_, sizeof(void*)*2);
if (v_stage_u2081_3210_ == 0)
{
lean_object* v_map_u2081_3211_; lean_object* v_map_u2082_3212_; lean_object* v___x_3213_; 
v_map_u2081_3211_ = lean_ctor_get(v_x_3208_, 0);
v_map_u2082_3212_ = lean_ctor_get(v_x_3208_, 1);
v___x_3213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3211_, v_x_3209_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_3212_, v_x_3209_);
return v___x_3214_;
}
else
{
return v___x_3213_;
}
}
else
{
lean_object* v_map_u2081_3215_; lean_object* v___x_3216_; 
v_map_u2081_3215_ = lean_ctor_get(v_x_3208_, 0);
v___x_3216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3215_, v_x_3209_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3217_, v_x_3218_);
lean_dec(v_x_3218_);
lean_dec_ref(v_x_3217_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_3220_, lean_object* v_n_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3240_; lean_object* v_val_3241_; lean_object* v___x_3243_; lean_object* v___y_3245_; lean_object* v_env_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3243_ = lean_st_ref_get(v___y_3223_);
v_env_3260_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_ref(v_env_3260_);
lean_dec(v___x_3243_);
v___x_3261_ = l_Lean_Environment_constants(v_env_3260_);
v___x_3262_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_3261_, v_n_3221_);
lean_dec_ref(v___x_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_box(0);
v___y_3245_ = v___x_3263_;
goto v___jp_3244_;
}
else
{
lean_object* v_val_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v_val_3264_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3265_ = l_Lean_ConstantInfo_levelParams(v_val_3264_);
lean_dec(v_val_3264_);
v___x_3266_ = lean_box(0);
v___x_3267_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_3265_, v___x_3266_);
v___y_3245_ = v___x_3267_;
goto v___jp_3244_;
}
v___jp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3228_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_3229_ = l_Lean_Expr_const___override(v_n_3221_, v___y_3226_);
v___x_3230_ = lean_unsigned_to_nat(32u);
v___x_3231_ = lean_mk_empty_array_with_capacity(v___x_3230_);
lean_dec_ref(v___x_3231_);
v___x_3232_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3233_ = lean_box(0);
v___x_3234_ = 0;
v___x_3235_ = l_Lean_MessageData_withExprHover(v___y_3227_, v___x_3229_, v___x_3232_, v___x_3233_, v___x_3233_, v___x_3233_, v___x_3234_);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3228_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v___x_3228_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
v___jp_3239_:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3242_, 0, v_val_3241_);
v___y_3226_ = v___y_3240_;
v___y_3227_ = v___x_3242_;
goto v___jp_3225_;
}
v___jp_3244_:
{
lean_object* v___x_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3259_; 
lean_inc(v_n_3221_);
v___x_3246_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_3221_, v___y_3223_);
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3259_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3259_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
if (lean_obj_tag(v_a_3247_) == 0)
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_3220_, v_n_3221_);
if (lean_obj_tag(v___x_3251_) == 0)
{
uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3252_ = 1;
lean_inc(v_n_3221_);
v___x_3253_ = l_Lean_Name_toString(v_n_3221_, v___x_3252_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 3);
lean_ctor_set(v___x_3249_, 0, v___x_3253_);
v___x_3255_ = v___x_3249_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
v___y_3226_ = v___y_3245_;
v___y_3227_ = v___x_3255_;
goto v___jp_3225_;
}
}
else
{
lean_object* v_val_3257_; 
lean_del_object(v___x_3249_);
v_val_3257_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_val_3257_);
lean_dec_ref_known(v___x_3251_, 1);
v___y_3240_ = v___y_3245_;
v_val_3241_ = v_val_3257_;
goto v___jp_3239_;
}
}
else
{
lean_object* v_val_3258_; 
lean_del_object(v___x_3249_);
v_val_3258_ = lean_ctor_get(v_a_3247_, 0);
lean_inc(v_val_3258_);
lean_dec_ref_known(v_a_3247_, 1);
v___y_3240_ = v___y_3245_;
v_val_3241_ = v_val_3258_;
goto v___jp_3239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_3268_, lean_object* v_n_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3268_, v_n_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v_firsts_3268_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
if (lean_obj_tag(v_x_3275_) == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = l_List_reverse___redArg(v_x_3276_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
else
{
lean_object* v_head_3282_; lean_object* v_tail_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3301_; 
v_head_3282_ = lean_ctor_get(v_x_3275_, 0);
v_tail_3283_ = lean_ctor_get(v_x_3275_, 1);
v_isSharedCheck_3301_ = !lean_is_exclusive(v_x_3275_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3285_ = v_x_3275_;
v_isShared_3286_ = v_isSharedCheck_3301_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_tail_3283_);
lean_inc(v_head_3282_);
lean_dec(v_x_3275_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3301_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; 
v___x_3287_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_3274_, v_head_3282_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v_x_3276_);
lean_ctor_set(v___x_3285_, 0, v_a_3288_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3288_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_x_3276_);
v___x_3290_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
v_x_3275_ = v_tail_3283_;
v_x_3276_ = v___x_3290_;
goto _start;
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_del_object(v___x_3285_);
lean_dec(v_tail_3283_);
lean_dec(v_x_3276_);
v_a_3293_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3287_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3287_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
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
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3302_, v_x_3303_, v_x_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v_a_3302_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_3309_, lean_object* v___x_3310_, lean_object* v___x_3311_, lean_object* v_a_3312_, lean_object* v_b_3313_){
_start:
{
lean_object* v_it_3315_; lean_object* v_startInclusive_3316_; lean_object* v_endExclusive_3317_; 
if (lean_obj_tag(v_a_3312_) == 0)
{
lean_object* v_currPos_3322_; lean_object* v_searcher_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3346_; 
v_currPos_3322_ = lean_ctor_get(v_a_3312_, 0);
v_searcher_3323_ = lean_ctor_get(v_a_3312_, 1);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_a_3312_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3325_ = v_a_3312_;
v_isShared_3326_ = v_isSharedCheck_3346_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_searcher_3323_);
lean_inc(v_currPos_3322_);
lean_dec(v_a_3312_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3346_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
uint8_t v_decide_3327_; 
v_decide_3327_ = lean_nat_dec_eq(v_searcher_3323_, v___x_3311_);
if (v_decide_3327_ == 0)
{
uint32_t v___x_3328_; uint32_t v___x_3329_; uint8_t v___x_3330_; 
v___x_3328_ = 10;
v___x_3329_ = lean_string_utf8_get_fast(v_val_3309_, v_searcher_3323_);
v___x_3330_ = lean_uint32_dec_eq(v___x_3329_, v___x_3328_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3331_ = lean_string_utf8_next_fast(v_val_3309_, v_searcher_3323_);
lean_dec(v_searcher_3323_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v___x_3331_);
v___x_3333_ = v___x_3325_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_currPos_3322_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
v_a_3312_ = v___x_3333_;
goto _start;
}
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_slice_3339_; lean_object* v_nextIt_3341_; 
v___x_3336_ = lean_string_utf8_next_fast(v_val_3309_, v_searcher_3323_);
v___x_3337_ = lean_nat_sub(v___x_3336_, v_searcher_3323_);
v___x_3338_ = lean_nat_add(v_searcher_3323_, v___x_3337_);
lean_dec(v___x_3337_);
v_slice_3339_ = l_String_Slice_subslice_x21(v___x_3310_, v_currPos_3322_, v_searcher_3323_);
lean_inc(v___x_3338_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v___x_3338_);
lean_ctor_set(v___x_3325_, 0, v___x_3338_);
v_nextIt_3341_ = v___x_3325_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v___x_3338_);
v_nextIt_3341_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v_startInclusive_3342_; lean_object* v_endExclusive_3343_; 
v_startInclusive_3342_ = lean_ctor_get(v_slice_3339_, 0);
lean_inc(v_startInclusive_3342_);
v_endExclusive_3343_ = lean_ctor_get(v_slice_3339_, 1);
lean_inc(v_endExclusive_3343_);
lean_dec_ref(v_slice_3339_);
v_it_3315_ = v_nextIt_3341_;
v_startInclusive_3316_ = v_startInclusive_3342_;
v_endExclusive_3317_ = v_endExclusive_3343_;
goto v___jp_3314_;
}
}
}
else
{
lean_object* v___x_3345_; 
lean_del_object(v___x_3325_);
lean_dec(v_searcher_3323_);
v___x_3345_ = lean_box(1);
lean_inc(v___x_3311_);
v_it_3315_ = v___x_3345_;
v_startInclusive_3316_ = v_currPos_3322_;
v_endExclusive_3317_ = v___x_3311_;
goto v___jp_3314_;
}
}
}
else
{
lean_dec(v___x_3311_);
return v_b_3313_;
}
v___jp_3314_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_string_utf8_extract_fast(v_val_3309_, v_startInclusive_3316_, v_endExclusive_3317_);
lean_dec(v_endExclusive_3317_);
lean_dec(v_startInclusive_3316_);
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
v___x_3320_ = lean_array_push(v_b_3313_, v___x_3319_);
v_a_3312_ = v_it_3315_;
v_b_3313_ = v___x_3320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_3347_, lean_object* v___x_3348_, lean_object* v___x_3349_, lean_object* v_a_3350_, lean_object* v_b_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3347_, v___x_3348_, v___x_3349_, v_a_3350_, v_b_3351_);
lean_dec_ref(v___x_3348_);
lean_dec_ref(v_val_3347_);
return v_res_3352_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_3357_ = l_Lean_stringToMessageData(v___x_3356_);
return v___x_3357_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_3360_ = l_Lean_stringToMessageData(v___x_3359_);
return v___x_3360_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_3363_ = l_Lean_stringToMessageData(v___x_3362_);
return v___x_3363_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_3368_ = l_Lean_MessageData_ofFormat(v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
if (lean_obj_tag(v_x_3371_) == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = l_List_reverse___redArg(v_x_3372_);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
else
{
lean_object* v_head_3378_; lean_object* v_tail_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3476_; 
v_head_3378_ = lean_ctor_get(v_x_3371_, 0);
v_tail_3379_ = lean_ctor_get(v_x_3371_, 1);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_x_3371_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3381_ = v_x_3371_;
v_isShared_3382_ = v_isSharedCheck_3476_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_tail_3379_);
lean_inc(v_head_3378_);
lean_dec(v_x_3371_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3476_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v_snd_3396_; lean_object* v_fst_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3475_; 
v_snd_3396_ = lean_ctor_get(v_head_3378_, 1);
v_fst_3397_ = lean_ctor_get(v_head_3378_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_head_3378_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3399_ = v_head_3378_;
v_isShared_3400_ = v_isSharedCheck_3475_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_snd_3396_);
lean_inc(v_fst_3397_);
lean_dec(v_head_3378_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3475_;
goto v_resetjp_3398_;
}
v___jp_3383_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___y_3386_);
lean_ctor_set(v___x_3388_, 1, v___y_3387_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___y_3384_);
v___x_3390_ = l_Lean_MessageData_nestD(v___x_3389_);
lean_inc_ref(v___y_3385_);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___y_3385_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v_x_3372_);
lean_ctor_set(v___x_3381_, 0, v___x_3391_);
v___x_3393_ = v___x_3381_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_x_3372_);
v___x_3393_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
v_x_3371_ = v_tail_3379_;
v_x_3372_ = v___x_3393_;
goto _start;
}
}
v_resetjp_3398_:
{
lean_object* v_fst_3401_; lean_object* v_snd_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3474_; 
v_fst_3401_ = lean_ctor_get(v_snd_3396_, 0);
v_snd_3402_ = lean_ctor_get(v_snd_3396_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_snd_3396_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3404_ = v_snd_3396_;
v_isShared_3405_ = v_isSharedCheck_3474_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_snd_3402_);
lean_inc(v_fst_3401_);
lean_dec(v_snd_3396_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3474_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v_a_3429_; lean_object* v___y_3445_; lean_object* v___x_3454_; 
v___x_3454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3370_, v_fst_3397_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Lean_MessageData_nil;
v_a_3429_ = v___x_3455_;
goto v___jp_3428_;
}
else
{
lean_object* v_val_3456_; 
v_val_3456_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v___x_3454_, 1);
if (lean_obj_tag(v_val_3456_) == 0)
{
lean_object* v_size_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v_size_3457_ = lean_ctor_get(v_val_3456_, 0);
v___x_3458_ = lean_mk_empty_array_with_capacity(v_size_3457_);
v___x_3459_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_3458_, v_val_3456_);
v___x_3460_ = lean_array_get_size(v___x_3459_);
v___x_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = lean_nat_dec_eq(v___x_3460_, v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___y_3470_; uint8_t v___x_3472_; 
v___x_3467_ = lean_unsigned_to_nat(1u);
v___x_3468_ = lean_nat_sub(v___x_3460_, v___x_3467_);
v___x_3472_ = lean_nat_dec_le(v___x_3465_, v___x_3468_);
if (v___x_3472_ == 0)
{
lean_inc(v___x_3468_);
v___y_3470_ = v___x_3468_;
goto v___jp_3469_;
}
else
{
v___y_3470_ = v___x_3465_;
goto v___jp_3469_;
}
v___jp_3469_:
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_nat_dec_le(v___y_3470_, v___x_3468_);
if (v___x_3471_ == 0)
{
lean_dec(v___x_3468_);
lean_inc(v___y_3470_);
v___y_3462_ = v___y_3470_;
v___y_3463_ = v___y_3470_;
goto v___jp_3461_;
}
else
{
v___y_3462_ = v___y_3470_;
v___y_3463_ = v___x_3468_;
goto v___jp_3461_;
}
}
}
else
{
v___y_3445_ = v___x_3459_;
goto v___jp_3444_;
}
v___jp_3461_:
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_3460_, v___x_3459_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
v___y_3445_ = v___x_3464_;
goto v___jp_3444_;
}
}
else
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_MessageData_nil;
v_a_3429_ = v___x_3473_;
goto v___jp_3428_;
}
}
v___jp_3406_:
{
lean_object* v___x_3412_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 7);
lean_ctor_set(v___x_3404_, 1, v___y_3410_);
lean_ctor_set(v___x_3404_, 0, v___y_3408_);
v___x_3412_ = v___x_3404_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___y_3408_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v___y_3410_);
v___x_3412_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
if (lean_obj_tag(v_snd_3402_) == 0)
{
lean_object* v___x_3413_; 
lean_del_object(v___x_3399_);
v___x_3413_ = l_Lean_MessageData_nil;
v___y_3384_ = v___y_3407_;
v___y_3385_ = v___y_3409_;
v___y_3386_ = v___x_3412_;
v___y_3387_ = v___x_3413_;
goto v___jp_3383_;
}
else
{
lean_object* v_val_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v_val_3414_ = lean_ctor_get(v_snd_3402_, 0);
lean_inc_n(v_val_3414_, 2);
lean_dec_ref_known(v_snd_3402_, 1);
v___x_3415_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3416_ = lean_unsigned_to_nat(0u);
v___x_3417_ = lean_string_utf8_byte_size(v_val_3414_);
v___x_3418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3418_, 0, v_val_3414_);
lean_ctor_set(v___x_3418_, 1, v___x_3416_);
lean_ctor_set(v___x_3418_, 2, v___x_3417_);
v___x_3419_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_3420_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_3421_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3414_, v___x_3418_, v___x_3417_, v___x_3419_, v___x_3420_);
lean_dec_ref_known(v___x_3418_, 3);
lean_dec(v_val_3414_);
v___x_3422_ = lean_array_to_list(v___x_3421_);
v___x_3423_ = l_Lean_MessageData_joinSep(v___x_3422_, v___x_3415_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 7);
lean_ctor_set(v___x_3399_, 1, v___x_3423_);
lean_ctor_set(v___x_3399_, 0, v___x_3415_);
v___x_3425_ = v___x_3399_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
v___y_3384_ = v___y_3407_;
v___y_3385_ = v___y_3409_;
v___y_3386_ = v___x_3412_;
v___y_3387_ = v___x_3425_;
goto v___jp_3383_;
}
}
}
}
v___jp_3428_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3430_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_3431_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
lean_inc(v_fst_3397_);
v___x_3432_ = l_Lean_MessageData_ofName(v_fst_3397_);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3431_);
v___x_3435_ = 1;
v___x_3436_ = l_Lean_Name_toString(v_fst_3397_, v___x_3435_);
v___x_3437_ = lean_string_dec_eq(v___x_3436_, v_fst_3401_);
lean_dec_ref(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3438_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_3439_ = l_Lean_stringToMessageData(v_fst_3401_);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_3442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___y_3407_ = v_a_3429_;
v___y_3408_ = v___x_3434_;
v___y_3409_ = v___x_3430_;
v___y_3410_ = v___x_3442_;
goto v___jp_3406_;
}
else
{
lean_object* v___x_3443_; 
lean_dec(v_fst_3401_);
v___x_3443_ = l_Lean_MessageData_nil;
v___y_3407_ = v_a_3429_;
v___y_3408_ = v___x_3434_;
v___y_3409_ = v___x_3430_;
v___y_3410_ = v___x_3443_;
goto v___jp_3406_;
}
}
v___jp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_array_to_list(v___y_3445_);
v___x_3447_ = lean_box(0);
v___x_3448_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3369_, v___x_3446_, v___x_3447_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_3451_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_3452_ = l_Lean_MessageData_joinSep(v_a_3449_, v___x_3451_);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3450_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v_a_3429_ = v___x_3453_;
goto v___jp_3428_;
}
else
{
lean_del_object(v___x_3404_);
lean_dec(v_snd_3402_);
lean_dec(v_fst_3401_);
lean_del_object(v___x_3399_);
lean_dec(v_fst_3397_);
lean_del_object(v___x_3381_);
lean_dec(v_tail_3379_);
lean_dec(v_x_3372_);
return v___x_3448_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_x_3479_, lean_object* v_x_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3477_, v_a_3478_, v_x_3479_, v_x_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_a_3478_);
lean_dec(v_a_3477_);
return v_res_3484_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_3486_, lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3487_) == 1)
{
lean_object* v_pre_3488_; 
v_pre_3488_ = lean_ctor_get(v_x_3487_, 0);
if (lean_obj_tag(v_pre_3488_) == 0)
{
lean_object* v_str_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v_str_3489_ = lean_ctor_get(v_x_3487_, 1);
v___x_3490_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_3491_ = lean_string_dec_eq(v_str_3489_, v___x_3490_);
if (v___x_3491_ == 0)
{
return v___x_3491_;
}
else
{
return v_suppressElabErrors_3486_;
}
}
else
{
uint8_t v___x_3492_; 
v___x_3492_ = 0;
return v___x_3492_;
}
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = 0;
return v___x_3493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_3494_, lean_object* v_x_3495_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3496_; uint8_t v_res_3497_; lean_object* v_r_3498_; 
v_suppressElabErrors_boxed_3496_ = lean_unbox(v_suppressElabErrors_3494_);
v_res_3497_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_3496_, v_x_3495_);
lean_dec(v_x_3495_);
v_r_3498_ = lean_box(v_res_3497_);
return v_r_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_3499_, lean_object* v_msgData_3500_, uint8_t v_severity_3501_, uint8_t v_isSilent_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; uint8_t v___y_3572_; uint8_t v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3598_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; uint8_t v___y_3605_; uint8_t v___y_3606_; uint8_t v___x_3621_; uint8_t v___y_3623_; uint8_t v___x_3633_; 
v___x_3621_ = 2;
v___x_3633_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3501_, v___x_3621_);
if (v___x_3633_ == 0)
{
v___y_3623_ = v___x_3633_;
goto v___jp_3622_;
}
else
{
uint8_t v___x_3634_; 
lean_inc_ref(v_msgData_3500_);
v___x_3634_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3500_);
if (v___x_3634_ == 0)
{
v___y_3623_ = v___x_3634_;
goto v___jp_3622_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec_ref(v_msgData_3500_);
v___x_3635_ = lean_box(0);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
}
v___jp_3506_:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Elab_Command_getScope___redArg(v___y_3514_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_currNamespace_3517_; lean_object* v___x_3518_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v_currNamespace_3517_ = lean_ctor_get(v_a_3516_, 2);
lean_inc(v_currNamespace_3517_);
lean_dec(v_a_3516_);
v___x_3518_ = l_Lean_Elab_Command_getScope___redArg(v___y_3514_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3554_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3554_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3554_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_openDecls_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v_env_3528_; lean_object* v_messages_3529_; lean_object* v_scopes_3530_; lean_object* v_usedQuotCtxts_3531_; lean_object* v_nextMacroScope_3532_; lean_object* v_maxRecDepth_3533_; lean_object* v_ngen_3534_; lean_object* v_auxDeclNGen_3535_; lean_object* v_infoState_3536_; lean_object* v_traceState_3537_; lean_object* v_snapshotTasks_3538_; lean_object* v_prevLinterStates_3539_; lean_object* v_codeQualityEntryTasks_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3553_; 
v_openDecls_3523_ = lean_ctor_get(v_a_3519_, 3);
lean_inc(v_openDecls_3523_);
lean_dec(v_a_3519_);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v_currNamespace_3517_);
lean_ctor_set(v___x_3524_, 1, v_openDecls_3523_);
v___x_3525_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v___y_3513_);
lean_inc_ref(v___y_3512_);
lean_inc_ref(v___y_3508_);
v___x_3526_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3526_, 0, v___y_3508_);
lean_ctor_set(v___x_3526_, 1, v___y_3511_);
lean_ctor_set(v___x_3526_, 2, v___y_3507_);
lean_ctor_set(v___x_3526_, 3, v___y_3512_);
lean_ctor_set(v___x_3526_, 4, v___x_3525_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*5, v___y_3509_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*5 + 1, v___y_3510_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*5 + 2, v_isSilent_3502_);
v___x_3527_ = lean_st_ref_take(v___y_3514_);
v_env_3528_ = lean_ctor_get(v___x_3527_, 0);
v_messages_3529_ = lean_ctor_get(v___x_3527_, 1);
v_scopes_3530_ = lean_ctor_get(v___x_3527_, 2);
v_usedQuotCtxts_3531_ = lean_ctor_get(v___x_3527_, 3);
v_nextMacroScope_3532_ = lean_ctor_get(v___x_3527_, 4);
v_maxRecDepth_3533_ = lean_ctor_get(v___x_3527_, 5);
v_ngen_3534_ = lean_ctor_get(v___x_3527_, 6);
v_auxDeclNGen_3535_ = lean_ctor_get(v___x_3527_, 7);
v_infoState_3536_ = lean_ctor_get(v___x_3527_, 8);
v_traceState_3537_ = lean_ctor_get(v___x_3527_, 9);
v_snapshotTasks_3538_ = lean_ctor_get(v___x_3527_, 10);
v_prevLinterStates_3539_ = lean_ctor_get(v___x_3527_, 11);
v_codeQualityEntryTasks_3540_ = lean_ctor_get(v___x_3527_, 12);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3542_ = v___x_3527_;
v_isShared_3543_ = v_isSharedCheck_3553_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3540_);
lean_inc(v_prevLinterStates_3539_);
lean_inc(v_snapshotTasks_3538_);
lean_inc(v_traceState_3537_);
lean_inc(v_infoState_3536_);
lean_inc(v_auxDeclNGen_3535_);
lean_inc(v_ngen_3534_);
lean_inc(v_maxRecDepth_3533_);
lean_inc(v_nextMacroScope_3532_);
lean_inc(v_usedQuotCtxts_3531_);
lean_inc(v_scopes_3530_);
lean_inc(v_messages_3529_);
lean_inc(v_env_3528_);
lean_dec(v___x_3527_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3553_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3544_ = lean_box(0);
v___x_3545_ = l_Lean_MessageLog_add(v___x_3526_, v_messages_3529_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3545_);
v___x_3547_ = v___x_3542_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_env_3528_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_scopes_3530_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_usedQuotCtxts_3531_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_nextMacroScope_3532_);
lean_ctor_set(v_reuseFailAlloc_3552_, 5, v_maxRecDepth_3533_);
lean_ctor_set(v_reuseFailAlloc_3552_, 6, v_ngen_3534_);
lean_ctor_set(v_reuseFailAlloc_3552_, 7, v_auxDeclNGen_3535_);
lean_ctor_set(v_reuseFailAlloc_3552_, 8, v_infoState_3536_);
lean_ctor_set(v_reuseFailAlloc_3552_, 9, v_traceState_3537_);
lean_ctor_set(v_reuseFailAlloc_3552_, 10, v_snapshotTasks_3538_);
lean_ctor_set(v_reuseFailAlloc_3552_, 11, v_prevLinterStates_3539_);
lean_ctor_set(v_reuseFailAlloc_3552_, 12, v_codeQualityEntryTasks_3540_);
v___x_3547_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = lean_st_ref_put(v___y_3514_, v___x_3547_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3544_);
v___x_3550_ = v___x_3521_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3544_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v_currNamespace_3517_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3507_);
v_a_3555_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3518_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3518_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3507_);
v_a_3563_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3515_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3515_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
v___jp_3571_:
{
lean_object* v_fileName_3576_; lean_object* v_fileMap_3577_; uint8_t v_suppressElabErrors_3578_; lean_object* v___x_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3596_; 
v_fileName_3576_ = lean_ctor_get(v___y_3503_, 0);
v_fileMap_3577_ = lean_ctor_get(v___y_3503_, 1);
v_suppressElabErrors_3578_ = lean_ctor_get_uint8(v___y_3503_, sizeof(void*)*10);
v___x_3579_ = lean_box(v_suppressElabErrors_3578_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3580_, 0, v___x_3579_);
v___x_3581_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3500_);
v___x_3582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__6___redArg(v___x_3581_, v___y_3504_);
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3596_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3596_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_inc_ref_n(v_fileMap_3577_, 2);
v___x_3587_ = l_Lean_FileMap_toPosition(v_fileMap_3577_, v___y_3574_);
lean_dec(v___y_3574_);
v___x_3588_ = l_Lean_FileMap_toPosition(v_fileMap_3577_, v___y_3575_);
lean_dec(v___y_3575_);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
v___x_3590_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___closed__7));
if (v_suppressElabErrors_3578_ == 0)
{
lean_del_object(v___x_3585_);
lean_dec_ref(v___f_3580_);
v___y_3507_ = v___x_3589_;
v___y_3508_ = v_fileName_3576_;
v___y_3509_ = v___y_3572_;
v___y_3510_ = v___y_3573_;
v___y_3511_ = v___x_3587_;
v___y_3512_ = v___x_3590_;
v___y_3513_ = v_a_3583_;
v___y_3514_ = v___y_3504_;
goto v___jp_3506_;
}
else
{
uint8_t v___x_3591_; 
lean_inc(v_a_3583_);
v___x_3591_ = l_Lean_MessageData_hasTag(v___f_3580_, v_a_3583_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
lean_dec_ref_known(v___x_3589_, 1);
lean_dec_ref(v___x_3587_);
lean_dec(v_a_3583_);
v___x_3592_ = lean_box(0);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3592_);
v___x_3594_ = v___x_3585_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
else
{
lean_del_object(v___x_3585_);
v___y_3507_ = v___x_3589_;
v___y_3508_ = v_fileName_3576_;
v___y_3509_ = v___y_3572_;
v___y_3510_ = v___y_3573_;
v___y_3511_ = v___x_3587_;
v___y_3512_ = v___x_3590_;
v___y_3513_ = v_a_3583_;
v___y_3514_ = v___y_3504_;
goto v___jp_3506_;
}
}
}
}
v___jp_3597_:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Syntax_getTailPos_x3f(v___y_3600_, v___y_3598_);
lean_dec(v___y_3600_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_inc(v___y_3601_);
v___y_3572_ = v___y_3598_;
v___y_3573_ = v___y_3599_;
v___y_3574_ = v___y_3601_;
v___y_3575_ = v___y_3601_;
goto v___jp_3571_;
}
else
{
lean_object* v_val_3603_; 
v_val_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_val_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___y_3572_ = v___y_3598_;
v___y_3573_ = v___y_3599_;
v___y_3574_ = v___y_3601_;
v___y_3575_ = v_val_3603_;
goto v___jp_3571_;
}
}
v___jp_3604_:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_Elab_Command_getRef___redArg(v___y_3503_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v_ref_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v_ref_3609_ = l_Lean_replaceRef(v_ref_3499_, v_a_3608_);
lean_dec(v_a_3608_);
v___x_3610_ = l_Lean_Syntax_getPos_x3f(v_ref_3609_, v___y_3605_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_unsigned_to_nat(0u);
v___y_3598_ = v___y_3605_;
v___y_3599_ = v___y_3606_;
v___y_3600_ = v_ref_3609_;
v___y_3601_ = v___x_3611_;
goto v___jp_3597_;
}
else
{
lean_object* v_val_3612_; 
v_val_3612_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_val_3612_);
lean_dec_ref_known(v___x_3610_, 1);
v___y_3598_ = v___y_3605_;
v___y_3599_ = v___y_3606_;
v___y_3600_ = v_ref_3609_;
v___y_3601_ = v_val_3612_;
goto v___jp_3597_;
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v_msgData_3500_);
v_a_3613_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3607_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3607_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
v___jp_3622_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v_scopes_3626_; lean_object* v___x_3627_; lean_object* v_opts_3628_; uint8_t v___x_3629_; uint8_t v___x_3630_; 
v___x_3624_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3625_ = lean_st_ref_get(v___y_3504_);
v_scopes_3626_ = lean_ctor_get(v___x_3625_, 2);
lean_inc(v_scopes_3626_);
lean_dec(v___x_3625_);
v___x_3627_ = l_List_head_x21___redArg(v___x_3624_, v_scopes_3626_);
lean_dec(v_scopes_3626_);
v_opts_3628_ = lean_ctor_get(v___x_3627_, 1);
lean_inc_ref(v_opts_3628_);
lean_dec(v___x_3627_);
v___x_3629_ = 1;
v___x_3630_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3501_, v___x_3629_);
if (v___x_3630_ == 0)
{
lean_dec_ref(v_opts_3628_);
v___y_3605_ = v___y_3623_;
v___y_3606_ = v_severity_3501_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3631_ = l_Lean_warningAsError;
v___x_3632_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__17(v_opts_3628_, v___x_3631_);
lean_dec_ref(v_opts_3628_);
if (v___x_3632_ == 0)
{
v___y_3605_ = v___y_3623_;
v___y_3606_ = v_severity_3501_;
goto v___jp_3604_;
}
else
{
v___y_3605_ = v___y_3623_;
v___y_3606_ = v___x_3621_;
goto v___jp_3604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_3637_, lean_object* v_msgData_3638_, lean_object* v_severity_3639_, lean_object* v_isSilent_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
uint8_t v_severity_boxed_3644_; uint8_t v_isSilent_boxed_3645_; lean_object* v_res_3646_; 
v_severity_boxed_3644_ = lean_unbox(v_severity_3639_);
v_isSilent_boxed_3645_ = lean_unbox(v_isSilent_3640_);
v_res_3646_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3637_, v_msgData_3638_, v_severity_boxed_3644_, v_isSilent_boxed_3645_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v_ref_3637_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_3647_, uint8_t v_severity_3648_, uint8_t v_isSilent_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Elab_Command_getRef___redArg(v___y_3650_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_3654_, v_msgData_3647_, v_severity_3648_, v_isSilent_3649_, v___y_3650_, v___y_3651_);
lean_dec(v_a_3654_);
return v___x_3655_;
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref(v_msgData_3647_);
v_a_3656_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3653_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3653_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
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
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_3664_, lean_object* v_severity_3665_, lean_object* v_isSilent_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_severity_boxed_3670_; uint8_t v_isSilent_boxed_3671_; lean_object* v_res_3672_; 
v_severity_boxed_3670_ = lean_unbox(v_severity_3665_);
v_isSilent_boxed_3671_ = lean_unbox(v_isSilent_3666_);
v_res_3672_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3664_, v_severity_boxed_3670_, v_isSilent_boxed_3671_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v___x_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = 0;
v___x_3678_ = 0;
v___x_3679_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3673_, v___x_3677_, v___x_3678_, v___y_3674_, v___y_3675_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_3685_, lean_object* v_x_3686_){
_start:
{
if (lean_obj_tag(v_x_3686_) == 0)
{
lean_object* v_k_3688_; lean_object* v_v_3689_; lean_object* v_l_3690_; lean_object* v_r_3691_; lean_object* v___x_3692_; lean_object* v_a_3693_; lean_object* v_a_3694_; lean_object* v___x_3695_; 
v_k_3688_ = lean_ctor_get(v_x_3686_, 1);
lean_inc(v_k_3688_);
v_v_3689_ = lean_ctor_get(v_x_3686_, 2);
lean_inc(v_v_3689_);
v_l_3690_ = lean_ctor_get(v_x_3686_, 3);
lean_inc(v_l_3690_);
v_r_3691_ = lean_ctor_get(v_x_3686_, 4);
lean_inc(v_r_3691_);
lean_dec_ref_known(v_x_3686_, 5);
v___x_3692_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3685_, v_l_3690_);
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3692_);
v_a_3694_ = lean_ctor_get(v_a_3693_, 0);
lean_inc(v_a_3694_);
lean_dec(v_a_3693_);
v___x_3695_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3688_, v_v_3689_, v_a_3694_);
v_init_3685_ = v___x_3695_;
v_x_3686_ = v_r_3691_;
goto _start;
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_init_3685_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
return v___x_3698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_3699_, lean_object* v_x_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3699_, v_x_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_3703_, lean_object* v_x1_3704_, lean_object* v_x2_3705_){
_start:
{
lean_object* v_fst_3706_; lean_object* v_fst_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v_fst_3706_ = lean_ctor_get(v_x1_3704_, 0);
lean_inc(v_fst_3706_);
lean_dec_ref(v_x1_3704_);
v_fst_3707_ = lean_ctor_get(v_x2_3705_, 0);
lean_inc(v_fst_3707_);
lean_dec_ref(v_x2_3705_);
v___x_3708_ = l_Lean_Name_toString(v_fst_3706_, v___x_3703_);
v___x_3709_ = l_Lean_Name_toString(v_fst_3707_, v___x_3703_);
v___x_3710_ = lean_string_dec_lt(v___x_3708_, v___x_3709_);
lean_dec_ref(v___x_3709_);
lean_dec_ref(v___x_3708_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_3711_, lean_object* v_x1_3712_, lean_object* v_x2_3713_){
_start:
{
uint8_t v___x_18317__boxed_3714_; uint8_t v_res_3715_; lean_object* v_r_3716_; 
v___x_18317__boxed_3714_ = lean_unbox(v___x_3711_);
v_res_3715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18317__boxed_3714_, v_x1_3712_, v_x2_3713_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_3717_, lean_object* v_pivot_3718_, lean_object* v_as_3719_, lean_object* v_i_3720_, lean_object* v_k_3721_){
_start:
{
uint8_t v___x_3722_; 
v___x_3722_ = lean_nat_dec_lt(v_k_3721_, v_hi_3717_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec(v_k_3721_);
lean_dec_ref(v_pivot_3718_);
v___x_3723_ = lean_array_fswap(v_as_3719_, v_i_3720_, v_hi_3717_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_i_3720_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; lean_object* v_fst_3726_; lean_object* v_fst_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3725_ = lean_array_fget_borrowed(v_as_3719_, v_k_3721_);
v_fst_3726_ = lean_ctor_get(v___x_3725_, 0);
v_fst_3727_ = lean_ctor_get(v_pivot_3718_, 0);
lean_inc(v_fst_3726_);
v___x_3728_ = l_Lean_Name_toString(v_fst_3726_, v___x_3722_);
lean_inc(v_fst_3727_);
v___x_3729_ = l_Lean_Name_toString(v_fst_3727_, v___x_3722_);
v___x_3730_ = lean_string_dec_lt(v___x_3728_, v___x_3729_);
lean_dec_ref(v___x_3729_);
lean_dec_ref(v___x_3728_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_unsigned_to_nat(1u);
v___x_3732_ = lean_nat_add(v_k_3721_, v___x_3731_);
lean_dec(v_k_3721_);
v_k_3721_ = v___x_3732_;
goto _start;
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3734_ = lean_array_fswap(v_as_3719_, v_i_3720_, v_k_3721_);
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = lean_nat_add(v_i_3720_, v___x_3735_);
lean_dec(v_i_3720_);
v___x_3737_ = lean_nat_add(v_k_3721_, v___x_3735_);
lean_dec(v_k_3721_);
v_as_3719_ = v___x_3734_;
v_i_3720_ = v___x_3736_;
v_k_3721_ = v___x_3737_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_3739_, lean_object* v_pivot_3740_, lean_object* v_as_3741_, lean_object* v_i_3742_, lean_object* v_k_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3739_, v_pivot_3740_, v_as_3741_, v_i_3742_, v_k_3743_);
lean_dec(v_hi_3739_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_3745_, lean_object* v_as_3746_, lean_object* v_lo_3747_, lean_object* v_hi_3748_){
_start:
{
lean_object* v___y_3750_; uint8_t v___x_3760_; 
v___x_3760_ = lean_nat_dec_lt(v_lo_3747_, v_hi_3748_);
if (v___x_3760_ == 0)
{
lean_dec(v_lo_3747_);
return v_as_3746_;
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_mid_3763_; lean_object* v___y_3765_; lean_object* v___y_3771_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3761_ = lean_nat_add(v_lo_3747_, v_hi_3748_);
v___x_3762_ = lean_unsigned_to_nat(1u);
v_mid_3763_ = lean_nat_shiftr(v___x_3761_, v___x_3762_);
lean_dec(v___x_3761_);
v___x_3776_ = lean_array_fget_borrowed(v_as_3746_, v_mid_3763_);
v___x_3777_ = lean_array_fget_borrowed(v_as_3746_, v_lo_3747_);
lean_inc(v___x_3777_);
lean_inc(v___x_3776_);
v___x_3778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3760_, v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
v___y_3771_ = v_as_3746_;
goto v___jp_3770_;
}
else
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_array_fswap(v_as_3746_, v_lo_3747_, v_mid_3763_);
v___y_3771_ = v___x_3779_;
goto v___jp_3770_;
}
v___jp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3766_ = lean_array_fget_borrowed(v___y_3765_, v_mid_3763_);
v___x_3767_ = lean_array_fget_borrowed(v___y_3765_, v_hi_3748_);
lean_inc(v___x_3767_);
lean_inc(v___x_3766_);
v___x_3768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3760_, v___x_3766_, v___x_3767_);
if (v___x_3768_ == 0)
{
lean_dec(v_mid_3763_);
v___y_3750_ = v___y_3765_;
goto v___jp_3749_;
}
else
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_array_fswap(v___y_3765_, v_mid_3763_, v_hi_3748_);
lean_dec(v_mid_3763_);
v___y_3750_ = v___x_3769_;
goto v___jp_3749_;
}
}
v___jp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
v___x_3772_ = lean_array_fget_borrowed(v___y_3771_, v_hi_3748_);
v___x_3773_ = lean_array_fget_borrowed(v___y_3771_, v_lo_3747_);
lean_inc(v___x_3773_);
lean_inc(v___x_3772_);
v___x_3774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_3760_, v___x_3772_, v___x_3773_);
if (v___x_3774_ == 0)
{
v___y_3765_ = v___y_3771_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_array_fswap(v___y_3771_, v_lo_3747_, v_hi_3748_);
v___y_3765_ = v___x_3775_;
goto v___jp_3764_;
}
}
}
v___jp_3749_:
{
lean_object* v_pivot_3751_; lean_object* v___x_3752_; lean_object* v_fst_3753_; lean_object* v_snd_3754_; uint8_t v___x_3755_; 
v_pivot_3751_ = lean_array_fget(v___y_3750_, v_hi_3748_);
lean_inc_n(v_lo_3747_, 2);
v___x_3752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3748_, v_pivot_3751_, v___y_3750_, v_lo_3747_, v_lo_3747_);
v_fst_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_fst_3753_);
v_snd_3754_ = lean_ctor_get(v___x_3752_, 1);
lean_inc(v_snd_3754_);
lean_dec_ref(v___x_3752_);
v___x_3755_ = lean_nat_dec_le(v_hi_3748_, v_fst_3753_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3745_, v_snd_3754_, v_lo_3747_, v_fst_3753_);
v___x_3757_ = lean_unsigned_to_nat(1u);
v___x_3758_ = lean_nat_add(v_fst_3753_, v___x_3757_);
lean_dec(v_fst_3753_);
v_as_3746_ = v___x_3756_;
v_lo_3747_ = v___x_3758_;
goto _start;
}
else
{
lean_dec(v_fst_3753_);
lean_dec(v_lo_3747_);
return v_snd_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_3780_, lean_object* v_as_3781_, lean_object* v_lo_3782_, lean_object* v_hi_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3780_, v_as_3781_, v_lo_3782_, v_hi_3783_);
lean_dec(v_hi_3783_);
lean_dec(v_n_3780_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_3785_, lean_object* v_x_3786_){
_start:
{
if (lean_obj_tag(v_x_3786_) == 0)
{
lean_object* v_k_3787_; lean_object* v_v_3788_; lean_object* v_l_3789_; lean_object* v_r_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_k_3787_ = lean_ctor_get(v_x_3786_, 1);
v_v_3788_ = lean_ctor_get(v_x_3786_, 2);
v_l_3789_ = lean_ctor_get(v_x_3786_, 3);
v_r_3790_ = lean_ctor_get(v_x_3786_, 4);
v___x_3791_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3785_, v_l_3789_);
lean_inc(v_v_3788_);
lean_inc(v_k_3787_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v_k_3787_);
lean_ctor_set(v___x_3792_, 1, v_v_3788_);
v___x_3793_ = lean_array_push(v___x_3791_, v___x_3792_);
v_init_3785_ = v___x_3793_;
v_x_3786_ = v_r_3790_;
goto _start;
}
else
{
return v_init_3785_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_3795_, lean_object* v_x_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3795_, v_x_3796_);
lean_dec(v_x_3796_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_3798_, size_t v_sz_3799_, size_t v_i_3800_, lean_object* v_b_3801_){
_start:
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_usize_dec_lt(v_i_3800_, v_sz_3799_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v_b_3801_);
return v___x_3804_;
}
else
{
lean_object* v_a_3805_; lean_object* v_fst_3806_; lean_object* v_snd_3807_; lean_object* v_found_3808_; size_t v___x_3809_; size_t v___x_3810_; 
v_a_3805_ = lean_array_uget_borrowed(v_as_3798_, v_i_3800_);
v_fst_3806_ = lean_ctor_get(v_a_3805_, 0);
v_snd_3807_ = lean_ctor_get(v_a_3805_, 1);
lean_inc(v_snd_3807_);
lean_inc(v_fst_3806_);
v_found_3808_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3806_, v_snd_3807_, v_b_3801_);
v___x_3809_ = ((size_t)1ULL);
v___x_3810_ = lean_usize_add(v_i_3800_, v___x_3809_);
v_i_3800_ = v___x_3810_;
v_b_3801_ = v_found_3808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_3812_, lean_object* v_sz_3813_, lean_object* v_i_3814_, lean_object* v_b_3815_, lean_object* v___y_3816_){
_start:
{
size_t v_sz_boxed_3817_; size_t v_i_boxed_3818_; lean_object* v_res_3819_; 
v_sz_boxed_3817_ = lean_unbox_usize(v_sz_3813_);
lean_dec(v_sz_3813_);
v_i_boxed_3818_ = lean_unbox_usize(v_i_3814_);
lean_dec(v_i_3814_);
v_res_3819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_3812_, v_sz_boxed_3817_, v_i_boxed_3818_, v_b_3815_);
lean_dec_ref(v_as_3812_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3820_, size_t v_sz_3821_, size_t v_i_3822_, lean_object* v_b_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
uint8_t v___x_3827_; 
v___x_3827_ = lean_usize_dec_lt(v_i_3822_, v_sz_3821_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_b_3823_);
return v___x_3828_;
}
else
{
lean_object* v_a_3829_; size_t v_sz_3830_; size_t v___x_3831_; lean_object* v___x_3832_; 
v_a_3829_ = lean_array_uget_borrowed(v_as_3820_, v_i_3822_);
v_sz_3830_ = lean_array_size(v_a_3829_);
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_3829_, v_sz_3830_, v___x_3831_, v_b_3823_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; size_t v___x_3834_; size_t v___x_3835_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
v___x_3834_ = ((size_t)1ULL);
v___x_3835_ = lean_usize_add(v_i_3822_, v___x_3834_);
v_i_3822_ = v___x_3835_;
v_b_3823_ = v_a_3833_;
goto _start;
}
else
{
return v___x_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3837_, lean_object* v_sz_3838_, lean_object* v_i_3839_, lean_object* v_b_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
size_t v_sz_boxed_3844_; size_t v_i_boxed_3845_; lean_object* v_res_3846_; 
v_sz_boxed_3844_ = lean_unbox_usize(v_sz_3838_);
lean_dec(v_sz_3838_);
v_i_boxed_3845_ = lean_unbox_usize(v_i_3839_);
lean_dec(v_i_3839_);
v_res_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3837_, v_sz_boxed_3844_, v_i_boxed_3845_, v_b_3840_, v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v_as_3837_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___y_3853_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v_env_3871_; lean_object* v___x_3872_; lean_object* v_toEnvExtension_3873_; lean_object* v_asyncMode_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v_a_3878_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v_a_3903_; lean_object* v_a_3904_; 
v___x_3868_ = lean_box(1);
v___x_3869_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3870_ = lean_st_ref_get(v___y_3850_);
v_env_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc_ref_n(v_env_3871_, 2);
lean_dec(v___x_3870_);
v___x_3872_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_3873_ = lean_ctor_get(v___x_3872_, 0);
v_asyncMode_3874_ = lean_ctor_get(v_toEnvExtension_3873_, 2);
v___x_3875_ = lean_box(0);
v___x_3876_ = 0;
v___x_3901_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3868_, v___x_3872_, v_env_3871_, v_asyncMode_3874_, v___x_3875_, v___x_3876_);
v___x_3902_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_3868_, v___x_3901_);
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref(v___x_3902_);
v_a_3904_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_a_3904_);
lean_dec(v_a_3903_);
v_a_3878_ = v_a_3904_;
goto v___jp_3877_;
v___jp_3852_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_array_to_list(v___y_3853_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
return v___x_3855_;
}
v___jp_3856_:
{
lean_object* v___x_3861_; 
v___x_3861_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_3858_, v___y_3857_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec(v___y_3858_);
v___y_3853_ = v___x_3861_;
goto v___jp_3852_;
}
v___jp_3862_:
{
uint8_t v___x_3867_; 
v___x_3867_ = lean_nat_dec_le(v___y_3866_, v___y_3865_);
if (v___x_3867_ == 0)
{
lean_dec(v___y_3865_);
lean_inc(v___y_3866_);
v___y_3857_ = v___y_3863_;
v___y_3858_ = v___y_3864_;
v___y_3859_ = v___y_3866_;
v___y_3860_ = v___y_3866_;
goto v___jp_3856_;
}
else
{
v___y_3857_ = v___y_3863_;
v___y_3858_ = v___y_3864_;
v___y_3859_ = v___y_3866_;
v___y_3860_ = v___y_3865_;
goto v___jp_3856_;
}
}
v___jp_3877_:
{
lean_object* v___x_3879_; lean_object* v_importedEntries_3880_; size_t v_sz_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v___x_3879_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3869_, v_toEnvExtension_3873_, v_env_3871_, v_asyncMode_3874_, v___x_3875_, v___x_3876_);
v_importedEntries_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc_ref(v_importedEntries_3880_);
lean_dec(v___x_3879_);
v_sz_3881_ = lean_array_size(v_importedEntries_3880_);
v___x_3882_ = ((size_t)0ULL);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_3880_, v_sz_3881_, v___x_3882_, v_a_3878_, v___y_3849_, v___y_3850_);
lean_dec_ref(v_importedEntries_3880_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_arr_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = lean_unsigned_to_nat(0u);
v___x_3886_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_3887_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_3886_, v_a_3884_);
lean_dec(v_a_3884_);
v___x_3888_ = lean_array_get_size(v_arr_3887_);
v___x_3889_ = lean_nat_dec_eq(v___x_3888_, v___x_3885_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; 
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = lean_nat_sub(v___x_3888_, v___x_3890_);
v___x_3892_ = lean_nat_dec_le(v___x_3885_, v___x_3891_);
if (v___x_3892_ == 0)
{
lean_inc(v___x_3891_);
v___y_3863_ = v_arr_3887_;
v___y_3864_ = v___x_3888_;
v___y_3865_ = v___x_3891_;
v___y_3866_ = v___x_3891_;
goto v___jp_3862_;
}
else
{
v___y_3863_ = v_arr_3887_;
v___y_3864_ = v___x_3888_;
v___y_3865_ = v___x_3891_;
v___y_3866_ = v___x_3885_;
goto v___jp_3862_;
}
}
else
{
v___y_3853_ = v_arr_3887_;
goto v___jp_3852_;
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
v_a_3893_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3883_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3883_);
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
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_3909_, lean_object* v_k_3910_, lean_object* v_fallback_3911_){
_start:
{
if (lean_obj_tag(v_t_3909_) == 0)
{
lean_object* v_k_3912_; lean_object* v_v_3913_; lean_object* v_l_3914_; lean_object* v_r_3915_; uint8_t v___x_3916_; 
v_k_3912_ = lean_ctor_get(v_t_3909_, 1);
v_v_3913_ = lean_ctor_get(v_t_3909_, 2);
v_l_3914_ = lean_ctor_get(v_t_3909_, 3);
v_r_3915_ = lean_ctor_get(v_t_3909_, 4);
v___x_3916_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3910_, v_k_3912_);
switch(v___x_3916_)
{
case 0:
{
v_t_3909_ = v_l_3914_;
goto _start;
}
case 1:
{
lean_inc(v_v_3913_);
return v_v_3913_;
}
default: 
{
v_t_3909_ = v_r_3915_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_3911_);
return v_fallback_3911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_3919_, lean_object* v_k_3920_, lean_object* v_fallback_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3919_, v_k_3920_, v_fallback_3921_);
lean_dec(v_fallback_3921_);
lean_dec(v_k_3920_);
lean_dec(v_t_3919_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_3923_, size_t v_sz_3924_, size_t v_i_3925_, lean_object* v_b_3926_){
_start:
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_usize_dec_lt(v_i_3925_, v_sz_3924_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_b_3926_);
return v___x_3929_;
}
else
{
lean_object* v_a_3930_; lean_object* v_fst_3931_; lean_object* v_snd_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; size_t v___x_3937_; size_t v___x_3938_; 
v_a_3930_ = lean_array_uget_borrowed(v_as_3923_, v_i_3925_);
v_fst_3931_ = lean_ctor_get(v_a_3930_, 0);
v_snd_3932_ = lean_ctor_get(v_a_3930_, 1);
v___x_3933_ = l_Lean_NameSet_empty;
v___x_3934_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3926_, v_snd_3932_, v___x_3933_);
lean_inc(v_fst_3931_);
v___x_3935_ = l_Lean_NameSet_insert(v___x_3934_, v_fst_3931_);
lean_inc(v_snd_3932_);
v___x_3936_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_3932_, v___x_3935_, v_b_3926_);
v___x_3937_ = ((size_t)1ULL);
v___x_3938_ = lean_usize_add(v_i_3925_, v___x_3937_);
v_i_3925_ = v___x_3938_;
v_b_3926_ = v___x_3936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_3940_, lean_object* v_sz_3941_, lean_object* v_i_3942_, lean_object* v_b_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3941_);
lean_dec(v_sz_3941_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3942_);
lean_dec(v_i_3942_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3940_, v_sz_boxed_3945_, v_i_boxed_3946_, v_b_3943_);
lean_dec_ref(v_as_3940_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_3948_, size_t v_sz_3949_, size_t v_i_3950_, lean_object* v_b_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = lean_usize_dec_lt(v_i_3950_, v_sz_3949_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3951_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; size_t v_sz_3958_; size_t v___x_3959_; lean_object* v___x_3960_; 
v_a_3957_ = lean_array_uget_borrowed(v_as_3948_, v_i_3950_);
v_sz_3958_ = lean_array_size(v_a_3957_);
v___x_3959_ = ((size_t)0ULL);
v___x_3960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_3957_, v_sz_3958_, v___x_3959_, v_b_3951_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; size_t v___x_3962_; size_t v___x_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
v___x_3962_ = ((size_t)1ULL);
v___x_3963_ = lean_usize_add(v_i_3950_, v___x_3962_);
v_i_3950_ = v___x_3963_;
v_b_3951_ = v_a_3961_;
goto _start;
}
else
{
return v___x_3960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_3965_, lean_object* v_sz_3966_, lean_object* v_i_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
size_t v_sz_boxed_3972_; size_t v_i_boxed_3973_; lean_object* v_res_3974_; 
v_sz_boxed_3972_ = lean_unbox_usize(v_sz_3966_);
lean_dec(v_sz_3966_);
v_i_boxed_3973_ = lean_unbox_usize(v_i_3967_);
lean_dec(v_i_3967_);
v_res_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_3965_, v_sz_boxed_3972_, v_i_boxed_3973_, v_b_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v_as_3965_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_3975_, size_t v_i_3976_, size_t v_stop_3977_, lean_object* v_b_3978_){
_start:
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_usize_dec_eq(v_i_3976_, v_stop_3977_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v_fst_3981_; lean_object* v_snd_3982_; lean_object* v___x_3983_; size_t v___x_3984_; size_t v___x_3985_; 
v___x_3980_ = lean_array_uget_borrowed(v_as_3975_, v_i_3976_);
v_fst_3981_ = lean_ctor_get(v___x_3980_, 0);
v_snd_3982_ = lean_ctor_get(v___x_3980_, 1);
lean_inc(v_snd_3982_);
lean_inc(v_fst_3981_);
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3981_, v_snd_3982_, v_b_3978_);
v___x_3984_ = ((size_t)1ULL);
v___x_3985_ = lean_usize_add(v_i_3976_, v___x_3984_);
v_i_3976_ = v___x_3985_;
v_b_3978_ = v___x_3983_;
goto _start;
}
else
{
return v_b_3978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_3987_, lean_object* v_i_3988_, lean_object* v_stop_3989_, lean_object* v_b_3990_){
_start:
{
size_t v_i_boxed_3991_; size_t v_stop_boxed_3992_; lean_object* v_res_3993_; 
v_i_boxed_3991_ = lean_unbox_usize(v_i_3988_);
lean_dec(v_i_3988_);
v_stop_boxed_3992_ = lean_unbox_usize(v_stop_3989_);
lean_dec(v_stop_3989_);
v_res_3993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_3987_, v_i_boxed_3991_, v_stop_boxed_3992_, v_b_3990_);
lean_dec_ref(v_as_3987_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_3994_, size_t v_i_3995_, size_t v_stop_3996_, lean_object* v_b_3997_){
_start:
{
lean_object* v___y_3999_; uint8_t v___x_4003_; 
v___x_4003_ = lean_usize_dec_eq(v_i_3995_, v_stop_3996_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; uint8_t v___x_4007_; 
v___x_4004_ = lean_array_uget_borrowed(v_as_3994_, v_i_3995_);
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = lean_array_get_size(v___x_4004_);
v___x_4007_ = lean_nat_dec_lt(v___x_4005_, v___x_4006_);
if (v___x_4007_ == 0)
{
v___y_3999_ = v_b_3997_;
goto v___jp_3998_;
}
else
{
size_t v___x_4008_; size_t v___x_4009_; lean_object* v___x_4010_; 
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = lean_usize_of_nat(v___x_4006_);
v___x_4010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_4004_, v___x_4008_, v___x_4009_, v_b_3997_);
v___y_3999_ = v___x_4010_;
goto v___jp_3998_;
}
}
else
{
return v_b_3997_;
}
v___jp_3998_:
{
size_t v___x_4000_; size_t v___x_4001_; 
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_add(v_i_3995_, v___x_4000_);
v_i_3995_ = v___x_4001_;
v_b_3997_ = v___y_3999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_4011_, lean_object* v_i_4012_, lean_object* v_stop_4013_, lean_object* v_b_4014_){
_start:
{
size_t v_i_boxed_4015_; size_t v_stop_boxed_4016_; lean_object* v_res_4017_; 
v_i_boxed_4015_ = lean_unbox_usize(v_i_4012_);
lean_dec(v_i_4012_);
v_stop_boxed_4016_ = lean_unbox_usize(v_stop_4013_);
lean_dec(v_stop_4013_);
v_res_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_4011_, v_i_boxed_4015_, v_stop_boxed_4016_, v_b_4014_);
lean_dec_ref(v_as_4011_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v_env_4024_; lean_object* v___x_4025_; lean_object* v_ext_4026_; lean_object* v_toEnvExtension_4027_; lean_object* v_asyncMode_4028_; uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v_categories_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4020_ = lean_box(1);
v___x_4021_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4022_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4023_ = lean_st_ref_get(v___y_4018_);
v_env_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc_ref_n(v_env_4024_, 2);
lean_dec(v___x_4023_);
v___x_4025_ = l_Lean_Parser_parserExtension;
v_ext_4026_ = lean_ctor_get(v___x_4025_, 1);
v_toEnvExtension_4027_ = lean_ctor_get(v_ext_4026_, 0);
v_asyncMode_4028_ = lean_ctor_get(v_toEnvExtension_4027_, 2);
v___x_4029_ = 0;
v___x_4030_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4022_, v___x_4025_, v_env_4024_, v_asyncMode_4028_, v___x_4029_);
v_categories_4031_ = lean_ctor_get(v___x_4030_, 2);
lean_inc_ref(v_categories_4031_);
lean_dec(v___x_4030_);
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4033_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4031_, v___x_4032_);
lean_dec_ref(v_categories_4031_);
if (lean_obj_tag(v___x_4033_) == 1)
{
lean_object* v_val_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4065_; 
v_val_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4065_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_val_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4065_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___y_4039_; lean_object* v___x_4048_; lean_object* v_toEnvExtension_4049_; lean_object* v_exportEntriesFn_4050_; lean_object* v_asyncMode_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v_importedEntries_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v_exported_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4048_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4049_ = lean_ctor_get(v___x_4048_, 0);
v_exportEntriesFn_4050_ = lean_ctor_get(v___x_4048_, 4);
v_asyncMode_4051_ = lean_ctor_get(v_toEnvExtension_4049_, 2);
v___x_4052_ = lean_box(0);
lean_inc_ref_n(v_env_4024_, 2);
v___x_4053_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4021_, v_toEnvExtension_4049_, v_env_4024_, v_asyncMode_4051_, v___x_4052_, v___x_4029_);
v_importedEntries_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc_ref(v_importedEntries_4054_);
lean_dec(v___x_4053_);
v___x_4055_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4020_, v___x_4048_, v_env_4024_, v_asyncMode_4051_, v___x_4052_, v___x_4029_);
lean_inc_ref(v_exportEntriesFn_4050_);
v___x_4056_ = lean_apply_2(v_exportEntriesFn_4050_, v_env_4024_, v___x_4055_);
v_exported_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_exported_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = lean_array_push(v_importedEntries_4054_, v_exported_4057_);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_array_get_size(v___x_4058_);
v___x_4061_ = lean_nat_dec_lt(v___x_4059_, v___x_4060_);
if (v___x_4061_ == 0)
{
lean_dec_ref(v___x_4058_);
v___y_4039_ = v___x_4020_;
goto v___jp_4038_;
}
else
{
size_t v___x_4062_; size_t v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = ((size_t)0ULL);
v___x_4063_ = lean_usize_of_nat(v___x_4060_);
v___x_4064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4058_, v___x_4062_, v___x_4063_, v___x_4020_);
lean_dec_ref(v___x_4058_);
v___y_4039_ = v___x_4064_;
goto v___jp_4038_;
}
v___jp_4038_:
{
lean_object* v_tables_4040_; lean_object* v_leadingTable_4041_; lean_object* v_trailingTable_4042_; lean_object* v_firstTokens_4043_; lean_object* v_firstTokens_4044_; lean_object* v___x_4046_; 
v_tables_4040_ = lean_ctor_get(v_val_4034_, 2);
v_leadingTable_4041_ = lean_ctor_get(v_tables_4040_, 0);
v_trailingTable_4042_ = lean_ctor_get(v_tables_4040_, 2);
lean_inc(v_trailingTable_4042_);
lean_inc(v_leadingTable_4041_);
lean_inc(v_val_4034_);
v_firstTokens_4043_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4034_, v_leadingTable_4041_, v___y_4039_);
v_firstTokens_4044_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4034_, v_trailingTable_4042_, v_firstTokens_4043_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set_tag(v___x_4036_, 0);
lean_ctor_set(v___x_4036_, 0, v_firstTokens_4044_);
v___x_4046_ = v___x_4036_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_firstTokens_4044_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_object* v___x_4066_; 
lean_dec(v___x_4033_);
lean_dec_ref(v_env_4024_);
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4020_);
return v___x_4066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4067_);
lean_dec(v___y_4067_);
return v_res_4069_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v_env_4079_; lean_object* v___x_4080_; lean_object* v_env_4081_; lean_object* v___x_4082_; lean_object* v_env_4083_; lean_object* v___x_4084_; lean_object* v_toEnvExtension_4085_; lean_object* v_exportEntriesFn_4086_; lean_object* v_asyncMode_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; lean_object* v_importedEntries_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4143_; 
v___x_4076_ = lean_box(1);
v___x_4077_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4078_ = lean_st_ref_get(v_a_4074_);
v_env_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc_ref(v_env_4079_);
lean_dec(v___x_4078_);
v___x_4080_ = lean_st_ref_get(v_a_4074_);
v_env_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4081_);
lean_dec(v___x_4080_);
v___x_4082_ = lean_st_ref_get(v_a_4074_);
v_env_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc_ref(v_env_4083_);
lean_dec(v___x_4082_);
v___x_4084_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4085_ = lean_ctor_get(v___x_4084_, 0);
v_exportEntriesFn_4086_ = lean_ctor_get(v___x_4084_, 4);
v_asyncMode_4087_ = lean_ctor_get(v_toEnvExtension_4085_, 2);
v___x_4088_ = lean_box(0);
v___x_4089_ = 0;
v___x_4090_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4077_, v_toEnvExtension_4085_, v_env_4079_, v_asyncMode_4087_, v___x_4088_, v___x_4089_);
v_importedEntries_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4143_ == 0)
{
lean_object* v_unused_4144_; 
v_unused_4144_ = lean_ctor_get(v___x_4090_, 1);
lean_dec(v_unused_4144_);
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4143_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_importedEntries_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4143_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v_exported_4097_; lean_object* v___x_4098_; size_t v_sz_4099_; size_t v___x_4100_; lean_object* v___x_4101_; 
v___x_4095_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4076_, v___x_4084_, v_env_4083_, v_asyncMode_4087_, v___x_4088_, v___x_4089_);
lean_inc_ref(v_exportEntriesFn_4086_);
v___x_4096_ = lean_apply_2(v_exportEntriesFn_4086_, v_env_4081_, v___x_4095_);
v_exported_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_exported_4097_);
lean_dec_ref(v___x_4096_);
v___x_4098_ = lean_array_push(v_importedEntries_4091_, v_exported_4097_);
v_sz_4099_ = lean_array_size(v___x_4098_);
v___x_4100_ = ((size_t)0ULL);
v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_4098_, v_sz_4099_, v___x_4100_, v___x_4076_, v_a_4073_, v_a_4074_);
lean_dec_ref(v___x_4098_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v_a_4104_; lean_object* v___x_4105_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4103_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_4074_);
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref(v___x_4103_);
v___x_4105_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_4073_, v_a_4074_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4105_, 1);
v___x_4107_ = lean_box(0);
v___x_4108_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_4104_, v_a_4102_, v_a_4106_, v___x_4107_, v_a_4073_, v_a_4074_);
lean_dec(v_a_4102_);
lean_dec(v_a_4104_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4108_, 1);
v___x_4110_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_4111_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0_spec__1_spec__7_spec__18___closed__0);
v___x_4112_ = l_Lean_MessageData_joinSep(v_a_4109_, v___x_4111_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set_tag(v___x_4093_, 7);
lean_ctor_set(v___x_4093_, 1, v___x_4112_);
lean_ctor_set(v___x_4093_, 0, v___x_4111_);
v___x_4114_ = v___x_4093_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = l_Lean_MessageData_nestD(v___x_4114_);
v___x_4116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4110_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_4116_, v_a_4073_, v_a_4074_);
return v___x_4117_;
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_del_object(v___x_4093_);
v_a_4119_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4108_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4108_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_a_4104_);
lean_dec(v_a_4102_);
lean_del_object(v___x_4093_);
v_a_4127_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4105_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4105_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_del_object(v___x_4093_);
v_a_4135_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4101_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4101_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4145_, v_a_4146_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4150_, v_a_4151_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4154_, v_a_4155_, v_a_4156_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v___stx_4154_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_4159_, lean_object* v_t_4160_, lean_object* v_k_4161_, lean_object* v_fallback_4162_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4160_, v_k_4161_, v_fallback_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_4164_, lean_object* v_t_4165_, lean_object* v_k_4166_, lean_object* v_fallback_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_4164_, v_t_4165_, v_k_4166_, v_fallback_4167_);
lean_dec(v_fallback_4167_);
lean_dec(v_k_4166_);
lean_dec(v_t_4165_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_4169_, size_t v_sz_4170_, size_t v_i_4171_, lean_object* v_b_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4169_, v_sz_4170_, v_i_4171_, v_b_4172_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_4177_, lean_object* v_sz_4178_, lean_object* v_i_4179_, lean_object* v_b_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
size_t v_sz_boxed_4184_; size_t v_i_boxed_4185_; lean_object* v_res_4186_; 
v_sz_boxed_4184_ = lean_unbox_usize(v_sz_4178_);
lean_dec(v_sz_4178_);
v_i_boxed_4185_ = lean_unbox_usize(v_i_4179_);
lean_dec(v_i_4179_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4177_, v_sz_boxed_4184_, v_i_boxed_4185_, v_b_4180_, v___y_4181_, v___y_4182_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec_ref(v_as_4177_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4188_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_4195_, lean_object* v___x_4196_, lean_object* v___x_4197_, lean_object* v_inst_4198_, lean_object* v_R_4199_, lean_object* v_a_4200_, lean_object* v_b_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_4195_, v___x_4196_, v___x_4197_, v_a_4200_, v_b_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_4203_, lean_object* v___x_4204_, lean_object* v___x_4205_, lean_object* v_inst_4206_, lean_object* v_R_4207_, lean_object* v_a_4208_, lean_object* v_b_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_4203_, v___x_4204_, v___x_4205_, v_inst_4206_, v_R_4207_, v_a_4208_, v_b_4209_);
lean_dec_ref(v___x_4204_);
lean_dec_ref(v_val_4203_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_4211_, lean_object* v_t_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_4211_, v_t_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_4214_, lean_object* v_as_4215_, lean_object* v_lo_4216_, lean_object* v_hi_4217_, lean_object* v_w_4218_, lean_object* v_hlo_4219_, lean_object* v_hhi_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_4214_, v_as_4215_, v_lo_4216_, v_hi_4217_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_4222_, lean_object* v_as_4223_, lean_object* v_lo_4224_, lean_object* v_hi_4225_, lean_object* v_w_4226_, lean_object* v_hlo_4227_, lean_object* v_hhi_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_4222_, v_as_4223_, v_lo_4224_, v_hi_4225_, v_w_4226_, v_hlo_4227_, v_hhi_4228_);
lean_dec(v_hi_4225_);
lean_dec(v_n_4222_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_4230_, lean_object* v_x_4231_, lean_object* v_x_4232_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_4231_, v_x_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4234_, lean_object* v_x_4235_, lean_object* v_x_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_4234_, v_x_4235_, v_x_4236_);
lean_dec(v_x_4236_);
lean_dec_ref(v_x_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_4238_, v___y_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_4248_, lean_object* v_t_4249_, lean_object* v_k_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_4249_, v_k_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_4252_, lean_object* v_t_4253_, lean_object* v_k_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_4252_, v_t_4253_, v_k_4254_);
lean_dec(v_k_4254_);
lean_dec(v_t_4253_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_4257_, v_x_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_4260_, lean_object* v_x_4261_, lean_object* v_x_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_4260_, v_x_4261_, v_x_4262_);
lean_dec(v_x_4262_);
lean_dec_ref(v_x_4261_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_4264_, lean_object* v_lo_4265_, lean_object* v_hi_4266_, lean_object* v_hhi_4267_, lean_object* v_pivot_4268_, lean_object* v_as_4269_, lean_object* v_i_4270_, lean_object* v_k_4271_, lean_object* v_ilo_4272_, lean_object* v_ik_4273_, lean_object* v_w_4274_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_4266_, v_pivot_4268_, v_as_4269_, v_i_4270_, v_k_4271_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_4276_, lean_object* v_lo_4277_, lean_object* v_hi_4278_, lean_object* v_hhi_4279_, lean_object* v_pivot_4280_, lean_object* v_as_4281_, lean_object* v_i_4282_, lean_object* v_k_4283_, lean_object* v_ilo_4284_, lean_object* v_ik_4285_, lean_object* v_w_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_4276_, v_lo_4277_, v_hi_4278_, v_hhi_4279_, v_pivot_4280_, v_as_4281_, v_i_4282_, v_k_4283_, v_ilo_4284_, v_ik_4285_, v_w_4286_);
lean_dec(v_hi_4278_);
lean_dec(v_lo_4277_);
lean_dec(v_n_4276_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_4288_, size_t v_sz_4289_, size_t v_i_4290_, lean_object* v_b_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4288_, v_sz_4289_, v_i_4290_, v_b_4291_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_4296_, lean_object* v_sz_4297_, lean_object* v_i_4298_, lean_object* v_b_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
size_t v_sz_boxed_4303_; size_t v_i_boxed_4304_; lean_object* v_res_4305_; 
v_sz_boxed_4303_ = lean_unbox_usize(v_sz_4297_);
lean_dec(v_sz_4297_);
v_i_boxed_4304_ = lean_unbox_usize(v_i_4298_);
lean_dec(v_i_4298_);
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4296_, v_sz_boxed_4303_, v_i_boxed_4304_, v_b_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec_ref(v_as_4296_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_4306_, lean_object* v_t_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4306_, v_t_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_4309_, lean_object* v_t_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_4309_, v_t_4310_);
lean_dec(v_t_4310_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_4312_, lean_object* v_as_4313_, lean_object* v_lo_4314_, lean_object* v_hi_4315_, lean_object* v_w_4316_, lean_object* v_hlo_4317_, lean_object* v_hhi_4318_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4312_, v_as_4313_, v_lo_4314_, v_hi_4315_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_4320_, lean_object* v_as_4321_, lean_object* v_lo_4322_, lean_object* v_hi_4323_, lean_object* v_w_4324_, lean_object* v_hlo_4325_, lean_object* v_hhi_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_4320_, v_as_4321_, v_lo_4322_, v_hi_4323_, v_w_4324_, v_hlo_4325_, v_hhi_4326_);
lean_dec(v_hi_4323_);
lean_dec(v_n_4320_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_4328_, lean_object* v_x_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4328_, v_x_4329_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_4334_, lean_object* v_x_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4334_, v_x_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_4340_, lean_object* v_x_4341_, size_t v_x_4342_, lean_object* v_x_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_4341_, v_x_4342_, v_x_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_, lean_object* v_x_4348_){
_start:
{
size_t v_x_19025__boxed_4349_; lean_object* v_res_4350_; 
v_x_19025__boxed_4349_ = lean_unbox_usize(v_x_4347_);
lean_dec(v_x_4347_);
v_res_4350_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_4345_, v_x_4346_, v_x_19025__boxed_4349_, v_x_4348_);
lean_dec(v_x_4348_);
lean_dec_ref(v_x_4346_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_4351_, lean_object* v_k_4352_, lean_object* v_x_4353_, lean_object* v_x_4354_, lean_object* v_x_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_4351_, v_k_4352_, v_x_4353_, v_x_4354_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_4357_, lean_object* v_k_4358_, lean_object* v_x_4359_, lean_object* v_x_4360_, lean_object* v_x_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_4357_, v_k_4358_, v_x_4359_, v_x_4360_, v_x_4361_);
lean_dec_ref(v_k_4358_);
lean_dec_ref(v_as_4357_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_4363_, lean_object* v_m_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_4364_, v_a_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_4367_, lean_object* v_m_4368_, lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_4367_, v_m_4368_, v_a_4369_);
lean_dec(v_a_4369_);
lean_dec_ref(v_m_4368_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_4371_, lean_object* v_lo_4372_, lean_object* v_hi_4373_, lean_object* v_hhi_4374_, lean_object* v_pivot_4375_, lean_object* v_as_4376_, lean_object* v_i_4377_, lean_object* v_k_4378_, lean_object* v_ilo_4379_, lean_object* v_ik_4380_, lean_object* v_w_4381_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4373_, v_pivot_4375_, v_as_4376_, v_i_4377_, v_k_4378_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_4383_, lean_object* v_lo_4384_, lean_object* v_hi_4385_, lean_object* v_hhi_4386_, lean_object* v_pivot_4387_, lean_object* v_as_4388_, lean_object* v_i_4389_, lean_object* v_k_4390_, lean_object* v_ilo_4391_, lean_object* v_ik_4392_, lean_object* v_w_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_4383_, v_lo_4384_, v_hi_4385_, v_hhi_4386_, v_pivot_4387_, v_as_4388_, v_i_4389_, v_k_4390_, v_ilo_4391_, v_ik_4392_, v_w_4393_);
lean_dec(v_hi_4385_);
lean_dec(v_lo_4384_);
lean_dec(v_n_4383_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_4395_, lean_object* v_keys_4396_, lean_object* v_vals_4397_, lean_object* v_heq_4398_, lean_object* v_i_4399_, lean_object* v_k_4400_){
_start:
{
lean_object* v___x_4401_; 
v___x_4401_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_4396_, v_vals_4397_, v_i_4399_, v_k_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_4402_, lean_object* v_keys_4403_, lean_object* v_vals_4404_, lean_object* v_heq_4405_, lean_object* v_i_4406_, lean_object* v_k_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_4402_, v_keys_4403_, v_vals_4404_, v_heq_4405_, v_i_4406_, v_k_4407_);
lean_dec(v_k_4407_);
lean_dec_ref(v_vals_4404_);
lean_dec_ref(v_keys_4403_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_4409_, lean_object* v_a_4410_, lean_object* v_x_4411_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_4410_, v_x_4411_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_4413_, lean_object* v_a_4414_, lean_object* v_x_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_4413_, v_a_4414_, v_x_4415_);
lean_dec(v_x_4415_);
lean_dec(v_a_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4431_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_4433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4434_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_4435_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4431_, v___x_4432_, v___x_4433_, v___x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_4442_ = l_Lean_addBuiltinDocString(v___x_4440_, v___x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_4473_ = l_Lean_addBuiltinDeclarationRanges(v___x_4471_, v___x_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_4476_, lean_object* v___x_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, uint8_t v_includeUnnamed_4480_, lean_object* v_x_4481_, lean_object* v_____s_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_fst_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4543_; 
v_fst_4488_ = lean_ctor_get(v_x_4481_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_x_4481_);
if (v_isSharedCheck_4543_ == 0)
{
lean_object* v_unused_4544_; 
v_unused_4544_ = lean_ctor_get(v_x_4481_, 1);
lean_dec(v_unused_4544_);
v___x_4490_ = v_x_4481_;
v_isShared_4491_ = v_isSharedCheck_4543_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_fst_4488_);
lean_dec(v_x_4481_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4543_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_userName_4493_; lean_object* v___y_4494_; lean_object* v___x_4528_; 
lean_inc(v_fst_4488_);
lean_inc_ref(v_env_4476_);
v___x_4528_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4476_, v_fst_4488_);
if (lean_obj_tag(v___x_4528_) == 1)
{
lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4536_; 
lean_del_object(v___x_4490_);
lean_dec(v_fst_4488_);
lean_dec(v___x_4477_);
lean_dec_ref(v_env_4476_);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4536_ == 0)
{
lean_object* v_unused_4537_; 
v_unused_4537_ = lean_ctor_get(v___x_4528_, 0);
lean_dec(v_unused_4537_);
v___x_4530_ = v___x_4528_;
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
else
{
lean_dec(v___x_4528_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v_____s_4482_);
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_____s_4482_);
v___x_4533_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
return v___x_4534_;
}
}
}
else
{
lean_object* v___x_4538_; 
lean_dec(v___x_4528_);
v___x_4538_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_4479_, v_fst_4488_);
if (lean_obj_tag(v___x_4538_) == 1)
{
lean_object* v_val_4539_; 
v_val_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_val_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v_userName_4493_ = v_val_4539_;
v___y_4494_ = v___y_4485_;
goto v___jp_4492_;
}
else
{
lean_dec(v___x_4538_);
if (v_includeUnnamed_4480_ == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
lean_del_object(v___x_4490_);
lean_dec(v_fst_4488_);
lean_dec(v___x_4477_);
lean_dec_ref(v_env_4476_);
v___x_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4540_, 0, v_____s_4482_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
return v___x_4541_;
}
else
{
lean_object* v___x_4542_; 
lean_inc(v_fst_4488_);
v___x_4542_ = l_Lean_Name_toString(v_fst_4488_, v_includeUnnamed_4480_);
v_userName_4493_ = v___x_4542_;
v___y_4494_ = v___y_4485_;
goto v___jp_4492_;
}
}
}
v___jp_4492_:
{
lean_object* v_ref_4495_; uint8_t v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v_ref_4495_ = lean_ctor_get(v___y_4494_, 2);
v___x_4496_ = 1;
v___x_4497_ = l_Lean_Options_empty;
v___x_4498_ = lean_box(0);
lean_inc(v_fst_4488_);
lean_inc_ref(v_env_4476_);
v___x_4499_ = l_Lean_findDocString_x3f(v_env_4476_, v_fst_4488_, v___x_4496_, v___x_4497_, v___x_4477_, v___x_4498_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4513_; 
lean_del_object(v___x_4490_);
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4513_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4513_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4511_; 
v___x_4504_ = l_Lean_NameSet_empty;
v___x_4505_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_4478_, v_fst_4488_, v___x_4504_);
lean_inc(v_fst_4488_);
v___x_4506_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_4476_, v_fst_4488_);
v___x_4507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4507_, 0, v_fst_4488_);
lean_ctor_set(v___x_4507_, 1, v_userName_4493_);
lean_ctor_set(v___x_4507_, 2, v___x_4505_);
lean_ctor_set(v___x_4507_, 3, v_a_4500_);
lean_ctor_set(v___x_4507_, 4, v___x_4506_);
v___x_4508_ = lean_array_push(v_____s_4482_, v___x_4507_);
v___x_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4509_);
v___x_4511_ = v___x_4502_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4509_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4527_; 
lean_dec_ref(v_userName_4493_);
lean_dec(v_fst_4488_);
lean_dec_ref(v_____s_4482_);
lean_dec_ref(v_env_4476_);
v_a_4514_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4516_ = v___x_4499_;
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4499_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4522_; 
v___x_4518_ = lean_io_error_to_string(v_a_4514_);
v___x_4519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
v___x_4520_ = l_Lean_MessageData_ofFormat(v___x_4519_);
lean_inc(v_ref_4495_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 1, v___x_4520_);
lean_ctor_set(v___x_4490_, 0, v_ref_4495_);
v___x_4522_ = v___x_4490_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_ref_4495_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4524_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4522_);
v___x_4524_ = v___x_4516_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_4545_, lean_object* v___x_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_includeUnnamed_4549_, lean_object* v_x_4550_, lean_object* v_____s_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
uint8_t v_includeUnnamed_boxed_4557_; lean_object* v_res_4558_; 
v_includeUnnamed_boxed_4557_ = lean_unbox(v_includeUnnamed_4549_);
v_res_4558_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4545_, v___x_4546_, v_a_4547_, v_a_4548_, v_includeUnnamed_boxed_4557_, v_x_4550_, v_____s_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v_a_4548_);
lean_dec(v_a_4547_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_4559_, size_t v_sz_4560_, size_t v_i_4561_, lean_object* v_b_4562_){
_start:
{
uint8_t v___x_4564_; 
v___x_4564_ = lean_usize_dec_lt(v_i_4561_, v_sz_4560_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_b_4562_);
return v___x_4565_;
}
else
{
lean_object* v_a_4566_; lean_object* v_fst_4567_; lean_object* v_snd_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; size_t v___x_4573_; size_t v___x_4574_; 
v_a_4566_ = lean_array_uget_borrowed(v_as_4559_, v_i_4561_);
v_fst_4567_ = lean_ctor_get(v_a_4566_, 0);
v_snd_4568_ = lean_ctor_get(v_a_4566_, 1);
v___x_4569_ = l_Lean_NameSet_empty;
v___x_4570_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4562_, v_fst_4567_, v___x_4569_);
lean_inc(v_snd_4568_);
v___x_4571_ = l_Lean_NameSet_insert(v___x_4570_, v_snd_4568_);
lean_inc(v_fst_4567_);
v___x_4572_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4567_, v___x_4571_, v_b_4562_);
v___x_4573_ = ((size_t)1ULL);
v___x_4574_ = lean_usize_add(v_i_4561_, v___x_4573_);
v_i_4561_ = v___x_4574_;
v_b_4562_ = v___x_4572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_4576_, lean_object* v_sz_4577_, lean_object* v_i_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_){
_start:
{
size_t v_sz_boxed_4581_; size_t v_i_boxed_4582_; lean_object* v_res_4583_; 
v_sz_boxed_4581_ = lean_unbox_usize(v_sz_4577_);
lean_dec(v_sz_4577_);
v_i_boxed_4582_ = lean_unbox_usize(v_i_4578_);
lean_dec(v_i_4578_);
v_res_4583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4576_, v_sz_boxed_4581_, v_i_boxed_4582_, v_b_4579_);
lean_dec_ref(v_as_4576_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_4584_, size_t v_sz_4585_, size_t v_i_4586_, lean_object* v_b_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v___x_4593_; 
v___x_4593_ = lean_usize_dec_lt(v_i_4586_, v_sz_4585_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
v___x_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4594_, 0, v_b_4587_);
return v___x_4594_;
}
else
{
lean_object* v_a_4595_; size_t v_sz_4596_; size_t v___x_4597_; lean_object* v___x_4598_; 
v_a_4595_ = lean_array_uget_borrowed(v_as_4584_, v_i_4586_);
v_sz_4596_ = lean_array_size(v_a_4595_);
v___x_4597_ = ((size_t)0ULL);
v___x_4598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_4595_, v_sz_4596_, v___x_4597_, v_b_4587_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; size_t v___x_4600_; size_t v___x_4601_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v___x_4600_ = ((size_t)1ULL);
v___x_4601_ = lean_usize_add(v_i_4586_, v___x_4600_);
v_i_4586_ = v___x_4601_;
v_b_4587_ = v_a_4599_;
goto _start;
}
else
{
return v___x_4598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_4603_, lean_object* v_sz_4604_, lean_object* v_i_4605_, lean_object* v_b_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
size_t v_sz_boxed_4612_; size_t v_i_boxed_4613_; lean_object* v_res_4614_; 
v_sz_boxed_4612_ = lean_unbox_usize(v_sz_4604_);
lean_dec(v_sz_4604_);
v_i_boxed_4613_ = lean_unbox_usize(v_i_4605_);
lean_dec(v_i_4605_);
v_res_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4603_, v_sz_boxed_4612_, v_i_boxed_4613_, v_b_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec_ref(v_as_4603_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_4615_, lean_object* v_keys_4616_, lean_object* v_vals_4617_, lean_object* v_i_4618_, lean_object* v_acc_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v___x_4625_; uint8_t v___x_4626_; 
v___x_4625_ = lean_array_get_size(v_keys_4616_);
v___x_4626_ = lean_nat_dec_lt(v_i_4618_, v___x_4625_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
lean_dec(v_i_4618_);
lean_dec_ref(v_f_4615_);
v___x_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_acc_4619_);
v___x_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
return v___x_4628_;
}
else
{
lean_object* v_k_4629_; lean_object* v_v_4630_; lean_object* v___x_4631_; 
v_k_4629_ = lean_array_fget_borrowed(v_keys_4616_, v_i_4618_);
v_v_4630_ = lean_array_fget_borrowed(v_vals_4617_, v_i_4618_);
lean_inc_ref(v_f_4615_);
lean_inc(v___y_4623_);
lean_inc_ref(v___y_4622_);
lean_inc(v___y_4621_);
lean_inc_ref(v___y_4620_);
lean_inc(v_v_4630_);
lean_inc(v_k_4629_);
v___x_4631_ = lean_apply_8(v_f_4615_, v_acc_4619_, v_k_4629_, v_v_4630_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, lean_box(0));
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
if (lean_obj_tag(v_a_4632_) == 0)
{
lean_dec_ref_known(v_a_4632_, 1);
lean_dec(v_i_4618_);
lean_dec_ref(v_f_4615_);
return v___x_4631_;
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
lean_dec_ref_known(v___x_4631_, 1);
v_a_4633_ = lean_ctor_get(v_a_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v_a_4632_, 1);
v___x_4634_ = lean_unsigned_to_nat(1u);
v___x_4635_ = lean_nat_add(v_i_4618_, v___x_4634_);
lean_dec(v_i_4618_);
v_i_4618_ = v___x_4635_;
v_acc_4619_ = v_a_4633_;
goto _start;
}
}
else
{
lean_dec(v_i_4618_);
lean_dec_ref(v_f_4615_);
return v___x_4631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_4637_, lean_object* v_keys_4638_, lean_object* v_vals_4639_, lean_object* v_i_4640_, lean_object* v_acc_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4637_, v_keys_4638_, v_vals_4639_, v_i_4640_, v_acc_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec_ref(v_vals_4639_);
lean_dec_ref(v_keys_4638_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_4648_, lean_object* v_as_4649_, size_t v_i_4650_, size_t v_stop_4651_, lean_object* v_b_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_a_4659_; lean_object* v___y_4664_; uint8_t v___x_4667_; 
v___x_4667_ = lean_usize_dec_eq(v_i_4650_, v_stop_4651_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; 
v___x_4668_ = lean_array_uget_borrowed(v_as_4649_, v_i_4650_);
switch(lean_obj_tag(v___x_4668_))
{
case 0:
{
lean_object* v_key_4669_; lean_object* v_val_4670_; lean_object* v___x_4671_; 
v_key_4669_ = lean_ctor_get(v___x_4668_, 0);
v_val_4670_ = lean_ctor_get(v___x_4668_, 1);
lean_inc_ref(v_f_4648_);
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
lean_inc(v___y_4654_);
lean_inc_ref(v___y_4653_);
lean_inc(v_val_4670_);
lean_inc(v_key_4669_);
v___x_4671_ = lean_apply_8(v_f_4648_, v_b_4652_, v_key_4669_, v_val_4670_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, lean_box(0));
v___y_4664_ = v___x_4671_;
goto v___jp_4663_;
}
case 1:
{
lean_object* v_node_4672_; lean_object* v___x_4673_; 
v_node_4672_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_node_4672_);
lean_inc_ref(v_f_4648_);
v___x_4673_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4648_, v_node_4672_, v_b_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
v___y_4664_ = v___x_4673_;
goto v___jp_4663_;
}
default: 
{
v_a_4659_ = v_b_4652_;
goto v___jp_4658_;
}
}
}
else
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
lean_dec_ref(v_f_4648_);
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_b_4652_);
v___x_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
return v___x_4675_;
}
v___jp_4658_:
{
size_t v___x_4660_; size_t v___x_4661_; 
v___x_4660_ = ((size_t)1ULL);
v___x_4661_ = lean_usize_add(v_i_4650_, v___x_4660_);
v_i_4650_ = v___x_4661_;
v_b_4652_ = v_a_4659_;
goto _start;
}
v___jp_4663_:
{
if (lean_obj_tag(v___y_4664_) == 0)
{
lean_object* v_a_4665_; 
v_a_4665_ = lean_ctor_get(v___y_4664_, 0);
if (lean_obj_tag(v_a_4665_) == 0)
{
lean_dec_ref(v_f_4648_);
return v___y_4664_;
}
else
{
lean_object* v_a_4666_; 
lean_inc_ref(v_a_4665_);
lean_dec_ref_known(v___y_4664_, 1);
v_a_4666_ = lean_ctor_get(v_a_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v_a_4665_, 1);
v_a_4659_ = v_a_4666_;
goto v___jp_4658_;
}
}
else
{
lean_dec_ref(v_f_4648_);
return v___y_4664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_4676_, lean_object* v_x_4677_, lean_object* v_x_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
if (lean_obj_tag(v_x_4677_) == 0)
{
lean_object* v_es_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4698_; 
v_es_4684_ = lean_ctor_get(v_x_4677_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_x_4677_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4686_ = v_x_4677_;
v_isShared_4687_ = v_isSharedCheck_4698_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_es_4684_);
lean_dec(v_x_4677_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4698_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4688_ = lean_unsigned_to_nat(0u);
v___x_4689_ = lean_array_get_size(v_es_4684_);
v___x_4690_ = lean_nat_dec_lt(v___x_4688_, v___x_4689_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4692_; 
lean_dec_ref(v_es_4684_);
lean_dec_ref(v_f_4676_);
if (v_isShared_4687_ == 0)
{
lean_ctor_set_tag(v___x_4686_, 1);
lean_ctor_set(v___x_4686_, 0, v_x_4678_);
v___x_4692_ = v___x_4686_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_x_4678_);
v___x_4692_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
lean_object* v___x_4693_; 
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
return v___x_4693_;
}
}
else
{
size_t v___x_4695_; size_t v___x_4696_; lean_object* v___x_4697_; 
lean_del_object(v___x_4686_);
v___x_4695_ = ((size_t)0ULL);
v___x_4696_ = lean_usize_of_nat(v___x_4689_);
v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4676_, v_es_4684_, v___x_4695_, v___x_4696_, v_x_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
lean_dec_ref(v_es_4684_);
return v___x_4697_;
}
}
}
else
{
lean_object* v_ks_4699_; lean_object* v_vs_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v_ks_4699_ = lean_ctor_get(v_x_4677_, 0);
lean_inc_ref(v_ks_4699_);
v_vs_4700_ = lean_ctor_get(v_x_4677_, 1);
lean_inc_ref(v_vs_4700_);
lean_dec_ref_known(v_x_4677_, 2);
v___x_4701_ = lean_unsigned_to_nat(0u);
v___x_4702_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4676_, v_ks_4699_, v_vs_4700_, v___x_4701_, v_x_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
lean_dec_ref(v_vs_4700_);
lean_dec_ref(v_ks_4699_);
return v___x_4702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_4703_, lean_object* v_x_4704_, lean_object* v_x_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4703_, v_x_4704_, v_x_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_4712_, lean_object* v_as_4713_, lean_object* v_i_4714_, lean_object* v_stop_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
size_t v_i_boxed_4722_; size_t v_stop_boxed_4723_; lean_object* v_res_4724_; 
v_i_boxed_4722_ = lean_unbox_usize(v_i_4714_);
lean_dec(v_i_4714_);
v_stop_boxed_4723_ = lean_unbox_usize(v_stop_4715_);
lean_dec(v_stop_4715_);
v_res_4724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4712_, v_as_4713_, v_i_boxed_4722_, v_stop_boxed_4723_, v_b_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v_as_4713_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_4725_, lean_object* v_s_4726_, lean_object* v_a_4727_, lean_object* v_b_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4734_, 0, v_a_4727_);
lean_ctor_set(v___x_4734_, 1, v_b_4728_);
lean_inc(v___y_4732_);
lean_inc_ref(v___y_4731_);
lean_inc(v___y_4730_);
lean_inc_ref(v___y_4729_);
v___x_4735_ = lean_apply_7(v_f_4725_, v___x_4734_, v_s_4726_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, lean_box(0));
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4762_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4762_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4762_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
if (lean_obj_tag(v_a_4736_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4750_; 
v_a_4740_ = lean_ctor_get(v_a_4736_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_a_4736_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4742_ = v_a_4736_;
v_isShared_4743_ = v_isSharedCheck_4750_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v_a_4736_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4750_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4747_; 
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4745_);
v___x_4747_ = v___x_4738_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4761_; 
v_a_4751_ = lean_ctor_get(v_a_4736_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_a_4736_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4753_ = v_a_4736_;
v_isShared_4754_ = v_isSharedCheck_4761_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v_a_4736_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4761_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4758_; 
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4756_);
v___x_4758_ = v___x_4738_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
v_a_4763_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4735_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4735_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_4771_, lean_object* v_s_4772_, lean_object* v_a_4773_, lean_object* v_b_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_4771_, v_s_4772_, v_a_4773_, v_b_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_4781_, lean_object* v_init_4782_, lean_object* v_f_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___f_4789_; lean_object* v___x_4790_; 
v___f_4789_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4789_, 0, v_f_4783_);
lean_inc_ref(v_map_4781_);
v___x_4790_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_4789_, v_map_4781_, v_init_4782_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4799_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4799_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4799_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_a_4795_; lean_object* v___x_4797_; 
v_a_4795_ = lean_ctor_get(v_a_4791_, 0);
lean_inc(v_a_4795_);
lean_dec(v_a_4791_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v_a_4795_);
v___x_4797_ = v___x_4793_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
v_a_4800_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4790_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4790_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_4808_, lean_object* v_init_4809_, lean_object* v_f_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4808_, v_init_4809_, v_f_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec_ref(v_map_4808_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_4817_){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v_env_4823_; lean_object* v___x_4824_; lean_object* v_ext_4825_; lean_object* v_toEnvExtension_4826_; lean_object* v_asyncMode_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v_categories_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4819_ = lean_box(1);
v___x_4820_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4821_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4822_ = lean_st_ref_get(v___y_4817_);
v_env_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref_n(v_env_4823_, 2);
lean_dec(v___x_4822_);
v___x_4824_ = l_Lean_Parser_parserExtension;
v_ext_4825_ = lean_ctor_get(v___x_4824_, 1);
v_toEnvExtension_4826_ = lean_ctor_get(v_ext_4825_, 0);
v_asyncMode_4827_ = lean_ctor_get(v_toEnvExtension_4826_, 2);
v___x_4828_ = 0;
v___x_4829_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4821_, v___x_4824_, v_env_4823_, v_asyncMode_4827_, v___x_4828_);
v_categories_4830_ = lean_ctor_get(v___x_4829_, 2);
lean_inc_ref(v_categories_4830_);
lean_dec(v___x_4829_);
v___x_4831_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4832_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4830_, v___x_4831_);
lean_dec_ref(v_categories_4830_);
if (lean_obj_tag(v___x_4832_) == 1)
{
lean_object* v_val_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4864_; 
v_val_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4864_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_val_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4864_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___y_4838_; lean_object* v___x_4847_; lean_object* v_toEnvExtension_4848_; lean_object* v_exportEntriesFn_4849_; lean_object* v_asyncMode_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v_importedEntries_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v_exported_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4847_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4848_ = lean_ctor_get(v___x_4847_, 0);
v_exportEntriesFn_4849_ = lean_ctor_get(v___x_4847_, 4);
v_asyncMode_4850_ = lean_ctor_get(v_toEnvExtension_4848_, 2);
v___x_4851_ = lean_box(0);
lean_inc_ref_n(v_env_4823_, 2);
v___x_4852_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4820_, v_toEnvExtension_4848_, v_env_4823_, v_asyncMode_4850_, v___x_4851_, v___x_4828_);
v_importedEntries_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc_ref(v_importedEntries_4853_);
lean_dec(v___x_4852_);
v___x_4854_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4819_, v___x_4847_, v_env_4823_, v_asyncMode_4850_, v___x_4851_, v___x_4828_);
lean_inc_ref(v_exportEntriesFn_4849_);
v___x_4855_ = lean_apply_2(v_exportEntriesFn_4849_, v_env_4823_, v___x_4854_);
v_exported_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_exported_4856_);
lean_dec_ref(v___x_4855_);
v___x_4857_ = lean_array_push(v_importedEntries_4853_, v_exported_4856_);
v___x_4858_ = lean_unsigned_to_nat(0u);
v___x_4859_ = lean_array_get_size(v___x_4857_);
v___x_4860_ = lean_nat_dec_lt(v___x_4858_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_dec_ref(v___x_4857_);
v___y_4838_ = v___x_4819_;
goto v___jp_4837_;
}
else
{
size_t v___x_4861_; size_t v___x_4862_; lean_object* v___x_4863_; 
v___x_4861_ = ((size_t)0ULL);
v___x_4862_ = lean_usize_of_nat(v___x_4859_);
v___x_4863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4857_, v___x_4861_, v___x_4862_, v___x_4819_);
lean_dec_ref(v___x_4857_);
v___y_4838_ = v___x_4863_;
goto v___jp_4837_;
}
v___jp_4837_:
{
lean_object* v_tables_4839_; lean_object* v_leadingTable_4840_; lean_object* v_trailingTable_4841_; lean_object* v_firstTokens_4842_; lean_object* v_firstTokens_4843_; lean_object* v___x_4845_; 
v_tables_4839_ = lean_ctor_get(v_val_4833_, 2);
v_leadingTable_4840_ = lean_ctor_get(v_tables_4839_, 0);
v_trailingTable_4841_ = lean_ctor_get(v_tables_4839_, 2);
lean_inc(v_trailingTable_4841_);
lean_inc(v_leadingTable_4840_);
lean_inc(v_val_4833_);
v_firstTokens_4842_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4833_, v_leadingTable_4840_, v___y_4838_);
v_firstTokens_4843_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4833_, v_trailingTable_4841_, v_firstTokens_4842_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set_tag(v___x_4835_, 0);
lean_ctor_set(v___x_4835_, 0, v_firstTokens_4843_);
v___x_4845_ = v___x_4835_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_firstTokens_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_object* v___x_4865_; 
lean_dec(v___x_4832_);
lean_dec_ref(v_env_4823_);
v___x_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4819_);
return v___x_4865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4866_);
lean_dec(v___y_4866_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v_env_4881_; lean_object* v___x_4882_; lean_object* v_toEnvExtension_4883_; lean_object* v_exportEntriesFn_4884_; lean_object* v_asyncMode_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; lean_object* v___x_4888_; lean_object* v_importedEntries_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v_exported_4892_; lean_object* v___x_4893_; size_t v_sz_4894_; size_t v___x_4895_; lean_object* v___x_4896_; 
v___x_4877_ = lean_box(1);
v___x_4878_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4879_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4880_ = lean_st_ref_get(v_a_4875_);
v_env_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc_ref_n(v_env_4881_, 4);
lean_dec(v___x_4880_);
v___x_4882_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4883_ = lean_ctor_get(v___x_4882_, 0);
v_exportEntriesFn_4884_ = lean_ctor_get(v___x_4882_, 4);
v_asyncMode_4885_ = lean_ctor_get(v_toEnvExtension_4883_, 2);
v___x_4886_ = lean_box(0);
v___x_4887_ = 0;
v___x_4888_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4878_, v_toEnvExtension_4883_, v_env_4881_, v_asyncMode_4885_, v___x_4886_, v___x_4887_);
v_importedEntries_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc_ref(v_importedEntries_4889_);
lean_dec(v___x_4888_);
v___x_4890_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4877_, v___x_4882_, v_env_4881_, v_asyncMode_4885_, v___x_4886_, v___x_4887_);
lean_inc_ref(v_exportEntriesFn_4884_);
v___x_4891_ = lean_apply_2(v_exportEntriesFn_4884_, v_env_4881_, v___x_4890_);
v_exported_4892_ = lean_ctor_get(v___x_4891_, 0);
lean_inc(v_exported_4892_);
lean_dec_ref(v___x_4891_);
v___x_4893_ = lean_array_push(v_importedEntries_4889_, v_exported_4892_);
v_sz_4894_ = lean_array_size(v___x_4893_);
v___x_4895_ = ((size_t)0ULL);
v___x_4896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_4893_, v_sz_4894_, v___x_4895_, v___x_4877_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec_ref(v___x_4893_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4920_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4920_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4920_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v_ext_4902_; lean_object* v_toEnvExtension_4903_; lean_object* v_asyncMode_4904_; lean_object* v___x_4905_; lean_object* v_categories_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4901_ = l_Lean_Parser_parserExtension;
v_ext_4902_ = lean_ctor_get(v___x_4901_, 1);
v_toEnvExtension_4903_ = lean_ctor_get(v_ext_4902_, 0);
v_asyncMode_4904_ = lean_ctor_get(v_toEnvExtension_4903_, 2);
lean_inc_ref(v_env_4881_);
v___x_4905_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4879_, v___x_4901_, v_env_4881_, v_asyncMode_4904_, v___x_4887_);
v_categories_4906_ = lean_ctor_get(v___x_4905_, 2);
lean_inc_ref(v_categories_4906_);
lean_dec(v___x_4905_);
v___x_4907_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_4908_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4909_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4906_, v___x_4908_);
lean_dec_ref(v_categories_4906_);
if (lean_obj_tag(v___x_4909_) == 1)
{
lean_object* v_val_4910_; lean_object* v___x_4911_; lean_object* v_a_4912_; lean_object* v_kinds_4913_; lean_object* v___x_4914_; lean_object* v___f_4915_; lean_object* v___x_4916_; 
lean_del_object(v___x_4899_);
v_val_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_val_4910_);
lean_dec_ref_known(v___x_4909_, 1);
v___x_4911_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_4875_);
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4912_);
lean_dec_ref(v___x_4911_);
v_kinds_4913_ = lean_ctor_get(v_val_4910_, 1);
lean_inc_ref(v_kinds_4913_);
lean_dec(v_val_4910_);
v___x_4914_ = lean_box(v_includeUnnamed_4871_);
v___f_4915_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4915_, 0, v_env_4881_);
lean_closure_set(v___f_4915_, 1, v___x_4886_);
lean_closure_set(v___f_4915_, 2, v_a_4897_);
lean_closure_set(v___f_4915_, 3, v_a_4912_);
lean_closure_set(v___f_4915_, 4, v___x_4914_);
v___x_4916_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_4913_, v___x_4907_, v___f_4915_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec_ref(v_kinds_4913_);
return v___x_4916_;
}
else
{
lean_object* v___x_4918_; 
lean_dec(v___x_4909_);
lean_dec(v_a_4897_);
lean_dec_ref(v_env_4881_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4907_);
v___x_4918_ = v___x_4899_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4907_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec_ref(v_env_4881_);
v_a_4921_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4896_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4896_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
uint8_t v_includeUnnamed_boxed_4935_; lean_object* v_res_4936_; 
v_includeUnnamed_boxed_4935_ = lean_unbox(v_includeUnnamed_4929_);
v_res_4936_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_4935_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_4937_, size_t v_sz_4938_, size_t v_i_4939_, lean_object* v_b_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4937_, v_sz_4938_, v_i_4939_, v_b_4940_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_4947_, lean_object* v_sz_4948_, lean_object* v_i_4949_, lean_object* v_b_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
size_t v_sz_boxed_4956_; size_t v_i_boxed_4957_; lean_object* v_res_4958_; 
v_sz_boxed_4956_ = lean_unbox_usize(v_sz_4948_);
lean_dec(v_sz_4948_);
v_i_boxed_4957_ = lean_unbox_usize(v_i_4949_);
lean_dec(v_i_4949_);
v_res_4958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_4947_, v_sz_boxed_4956_, v_i_boxed_4957_, v_b_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec_ref(v_as_4947_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4962_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_4971_, lean_object* v_00_u03b2_4972_, lean_object* v_map_4973_, lean_object* v_init_4974_, lean_object* v_f_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4973_, v_init_4974_, v_f_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_4982_, lean_object* v_00_u03b2_4983_, lean_object* v_map_4984_, lean_object* v_init_4985_, lean_object* v_f_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_4982_, v_00_u03b2_4983_, v_map_4984_, v_init_4985_, v_f_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
lean_dec_ref(v_map_4984_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_4993_, lean_object* v_f_4994_, lean_object* v_init_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4994_, v_map_4993_, v_init_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_5002_, lean_object* v_f_5003_, lean_object* v_init_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_5002_, v_f_5003_, v_init_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec(v___y_5008_);
lean_dec_ref(v___y_5007_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_5011_, lean_object* v_00_u03c3_5012_, lean_object* v_00_u03b2_5013_, lean_object* v_map_5014_, lean_object* v_f_5015_, lean_object* v_init_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5015_, v_map_5014_, v_init_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_5023_, lean_object* v_00_u03c3_5024_, lean_object* v_00_u03b2_5025_, lean_object* v_map_5026_, lean_object* v_f_5027_, lean_object* v_init_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_5023_, v_00_u03c3_5024_, v_00_u03b2_5025_, v_map_5026_, v_f_5027_, v_init_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_5035_, lean_object* v_00_u03c3_5036_, lean_object* v_00_u03b1_5037_, lean_object* v_00_u03b2_5038_, lean_object* v_f_5039_, lean_object* v_x_5040_, lean_object* v_x_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5039_, v_x_5040_, v_x_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_5048_, lean_object* v_00_u03c3_5049_, lean_object* v_00_u03b1_5050_, lean_object* v_00_u03b2_5051_, lean_object* v_f_5052_, lean_object* v_x_5053_, lean_object* v_x_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_5048_, v_00_u03c3_5049_, v_00_u03b1_5050_, v_00_u03b2_5051_, v_f_5052_, v_x_5053_, v_x_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_5061_, lean_object* v_00_u03b2_5062_, lean_object* v_00_u03c3_5063_, lean_object* v_00_u03c3_5064_, lean_object* v_f_5065_, lean_object* v_as_5066_, size_t v_i_5067_, size_t v_stop_5068_, lean_object* v_b_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5065_, v_as_5066_, v_i_5067_, v_stop_5068_, v_b_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5076_, lean_object* v_00_u03b2_5077_, lean_object* v_00_u03c3_5078_, lean_object* v_00_u03c3_5079_, lean_object* v_f_5080_, lean_object* v_as_5081_, lean_object* v_i_5082_, lean_object* v_stop_5083_, lean_object* v_b_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
size_t v_i_boxed_5090_; size_t v_stop_boxed_5091_; lean_object* v_res_5092_; 
v_i_boxed_5090_ = lean_unbox_usize(v_i_5082_);
lean_dec(v_i_5082_);
v_stop_boxed_5091_ = lean_unbox_usize(v_stop_5083_);
lean_dec(v_stop_5083_);
v_res_5092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_5076_, v_00_u03b2_5077_, v_00_u03c3_5078_, v_00_u03c3_5079_, v_f_5080_, v_as_5081_, v_i_boxed_5090_, v_stop_boxed_5091_, v_b_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec_ref(v_as_5081_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_5093_, lean_object* v_00_u03c3_5094_, lean_object* v_00_u03b1_5095_, lean_object* v_00_u03b2_5096_, lean_object* v_f_5097_, lean_object* v_keys_5098_, lean_object* v_vals_5099_, lean_object* v_heq_5100_, lean_object* v_i_5101_, lean_object* v_acc_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v___x_5108_; 
v___x_5108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_5097_, v_keys_5098_, v_vals_5099_, v_i_5101_, v_acc_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_5109_, lean_object* v_00_u03c3_5110_, lean_object* v_00_u03b1_5111_, lean_object* v_00_u03b2_5112_, lean_object* v_f_5113_, lean_object* v_keys_5114_, lean_object* v_vals_5115_, lean_object* v_heq_5116_, lean_object* v_i_5117_, lean_object* v_acc_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_5109_, v_00_u03c3_5110_, v_00_u03b1_5111_, v_00_u03b2_5112_, v_f_5113_, v_keys_5114_, v_vals_5115_, v_heq_5116_, v_i_5117_, v_acc_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_vals_5115_);
lean_dec_ref(v_keys_5114_);
return v_res_5124_;
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
