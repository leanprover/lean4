// Lean compiler output
// Module: Lean.Elab.GuardMsgs
// Imports: public import Lean.Elab.Notation public import Lean.Server.CodeActions.Attr
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Message_isTrace(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Message_isTrace___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "guard_msgs"};
static const lean_object* l_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 116, 183, 228, 179, 151, 45, 148)}};
static const lean_ctor_object l_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(183, 103, 150, 225, 110, 223, 115, 232)}};
static const lean_object* l_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "When true, show a diff between expected and actual messages if they don't match. "};
static const lean_object* l_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value)}};
static const lean_object* l_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_guard__msgs_diff;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@ "};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "..."};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "info:"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "warning:"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "error:"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "trace:"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "guardMsgsFilterAction"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(20, 4, 244, 232, 164, 150, 223, 103)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value),LEAN_SCALAR_PTR_LITERAL(148, 15, 254, 184, 37, 99, 251, 84)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "drop"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 195, 191, 35, 155, 125, 225, 61)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pass"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(130, 109, 187, 122, 38, 7, 169, 2)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "guardMsgsFilterSeverity"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 215, 239, 32, 31, 172, 250, 25)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 247, 236, 102, 6, 79, 161, 127)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 63, 183, 36, 16, 73, 158, 237)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 92, 21, 183, 34, 222, 2, 74)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(127, 232, 111, 183, 142, 221, 154, 104)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(125, 222, 92, 133, 213, 211, 83, 105)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11_value;
static const lean_closure_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Message_isTrace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "guardMsgsSpecElt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 108, 205, 157, 13, 129, 29, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "guardMsgsFilter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 187, 182, 29, 56, 60, 165, 253)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "guardMsgsWhitespace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(8, 106, 1, 198, 8, 55, 77, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "guardMsgsOrdering"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 53, 236, 42, 85, 133, 64, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "guardMsgsPositions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(41, 241, 109, 166, 211, 83, 245, 15)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "guardMsgsSubstring"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(23, 68, 193, 70, 193, 109, 117, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(97, 134, 219, 90, 90, 45, 96, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(234, 149, 90, 50, 108, 230, 18, 172)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "guardMsgsPositionsArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(72, 235, 102, 225, 139, 166, 36, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "guardMsgsOrderingArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(126, 165, 201, 178, 250, 91, 17, 12)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(255, 187, 8, 190, 181, 123, 198, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sorted"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(242, 25, 158, 210, 170, 109, 109, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "guardMsgsWhitespaceArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(133, 245, 235, 68, 150, 72, 242, 178)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "normalized"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 250, 226, 34, 169, 84, 107, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(205, 87, 76, 243, 164, 59, 221, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "guardMsgsSpec"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__6_value),LEAN_SCALAR_PTR_LITERAL(172, 228, 141, 39, 164, 16, 16, 29)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7_value;
static const lean_array_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "GuardMsgs"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__3_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "GuardMsgFailure"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__3_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__3_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 139, 31, 76, 158, 95, 94, 217)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__3_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(83, 21, 237, 121, 74, 154, 128, 4)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_GuardMsgs_instTypeNameGuardMsgFailure = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\t\n"};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5;
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⏎\n"};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " \n"};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 3, .m_data = "⏎⏎\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "\t⏎\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⏎\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1;
static const lean_array_object l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2_value;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3_value;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0 = (const lean_object*)&l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0 = (const lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1 = (const lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0_value),((lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1_value)}};
static const lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2 = (const lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 65, .m_data = "❌️ Docstring on `#guard_msgs` does not match generated message:\n\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "---\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardMsgsCmd"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4_value),LEAN_SCALAR_PTR_LITERAL(80, 121, 62, 112, 73, 11, 102, 99)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabGuardMsgs"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 139, 31, 76, 158, 95, 94, 217)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 103, 231, 132, 249, 141, 167, 146)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(137) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(168) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(137) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(137) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/--\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n-/\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/-- "};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -/\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Update #guard_msgs with generated message"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "quickfix"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*10 + 0, .m_other = 10, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_ = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369____boxed(lean_object*);
static const lean_string_object l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PANIC"};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0_value;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "guardPanicCmd"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 189, 140, 114, 132, 102, 231, 43)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected a PANIC but none was found"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabGuardPanic"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 139, 31, 76, 158, 95, 94, 217)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 172, 183, 87, 120, 30, 187, 134)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((lean_object*)(l_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_52_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(lean_object* v_line_57_, lean_object* v_pos_58_){
_start:
{
lean_object* v_line_59_; lean_object* v_column_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_line_59_ = lean_ctor_get(v_pos_58_, 0);
lean_inc(v_line_59_);
v_column_60_ = lean_ctor_get(v_pos_58_, 1);
lean_inc(v_column_60_);
lean_dec_ref(v_pos_58_);
v___x_61_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0));
v___x_62_ = lean_nat_sub(v_line_59_, v_line_57_);
lean_dec(v_line_59_);
v___x_63_ = l_Nat_reprFast(v___x_62_);
v___x_64_ = lean_string_append(v___x_61_, v___x_63_);
lean_dec_ref(v___x_63_);
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1));
v___x_66_ = lean_string_append(v___x_64_, v___x_65_);
v___x_67_ = l_Nat_reprFast(v_column_60_);
v___x_68_ = lean_string_append(v___x_66_, v___x_67_);
lean_dec_ref(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___boxed(lean_object* v_line_69_, lean_object* v_pos_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_line_69_, v_pos_70_);
lean_dec(v_line_69_);
return v_res_71_;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_82_ = lean_string_utf8_byte_size(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(lean_object* v_msg_85_, lean_object* v_reportPos_x3f_86_){
_start:
{
lean_object* v___y_89_; lean_object* v___y_93_; uint8_t v___y_94_; lean_object* v___y_96_; uint8_t v___y_97_; uint32_t v___y_98_; lean_object* v_str_102_; lean_object* v_pos_114_; lean_object* v_endPos_115_; uint8_t v_severity_116_; lean_object* v_caption_117_; lean_object* v_data_118_; lean_object* v___x_119_; lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v_str_134_; lean_object* v_str_146_; lean_object* v___y_157_; lean_object* v_str_161_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_pos_114_ = lean_ctor_get(v_msg_85_, 1);
lean_inc_ref(v_pos_114_);
v_endPos_115_ = lean_ctor_get(v_msg_85_, 2);
lean_inc(v_endPos_115_);
v_severity_116_ = lean_ctor_get_uint8(v_msg_85_, sizeof(void*)*5 + 1);
v_caption_117_ = lean_ctor_get(v_msg_85_, 3);
v_data_118_ = lean_ctor_get(v_msg_85_, 4);
lean_inc(v_data_118_);
v___x_119_ = l_Lean_MessageData_toString(v_data_118_);
v___x_168_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_169_ = lean_string_dec_eq(v_caption_117_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11));
lean_inc_ref(v_caption_117_);
v___x_171_ = lean_string_append(v_caption_117_, v___x_170_);
v___x_172_ = lean_string_append(v___x_171_, v___x_119_);
lean_dec_ref(v___x_119_);
v_str_161_ = v___x_172_;
goto v___jp_160_;
}
else
{
v_str_161_ = v___x_119_;
goto v___jp_160_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_91_ = lean_string_append(v___y_89_, v___x_90_);
return v___x_91_;
}
v___jp_92_:
{
if (v___y_94_ == 0)
{
return v___y_93_;
}
else
{
v___y_89_ = v___y_93_;
goto v___jp_88_;
}
}
v___jp_95_:
{
uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 10;
v___x_100_ = lean_uint32_dec_eq(v___y_98_, v___x_99_);
if (v___x_100_ == 0)
{
v___y_89_ = v___y_96_;
goto v___jp_88_;
}
else
{
v___y_93_ = v___y_96_;
v___y_94_ = v___y_97_;
goto v___jp_92_;
}
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = lean_string_utf8_byte_size(v_str_102_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc_ref(v_str_102_);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v_str_102_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
v___x_107_ = l_String_Slice_Pos_prev_x3f(v___x_106_, v___x_103_);
if (lean_obj_tag(v___x_107_) == 0)
{
uint32_t v___x_108_; 
lean_dec_ref(v___x_106_);
v___x_108_ = 65;
v___y_96_ = v_str_102_;
v___y_97_ = v___x_105_;
v___y_98_ = v___x_108_;
goto v___jp_95_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref(v___x_107_);
v___x_110_ = l_String_Slice_Pos_get_x3f(v___x_106_, v_val_109_);
lean_dec(v_val_109_);
lean_dec_ref(v___x_106_);
if (lean_obj_tag(v___x_110_) == 0)
{
uint32_t v___x_111_; 
v___x_111_ = 65;
v___y_96_ = v_str_102_;
v___y_97_ = v___x_105_;
v___y_98_ = v___x_111_;
goto v___jp_95_;
}
else
{
lean_object* v_val_112_; uint32_t v___x_113_; 
v_val_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_112_);
lean_dec_ref(v___x_110_);
v___x_113_ = lean_unbox_uint32(v_val_112_);
lean_dec(v_val_112_);
v___y_96_ = v_str_102_;
v___y_97_ = v___x_105_;
v___y_98_ = v___x_113_;
goto v___jp_95_;
}
}
}
else
{
v___y_93_ = v_str_102_;
v___y_94_ = v___x_105_;
goto v___jp_92_;
}
}
v___jp_120_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_125_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_121_, v_pos_114_);
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
v___x_129_ = lean_string_append(v___x_128_, v___y_123_);
lean_dec_ref(v___y_123_);
v___x_130_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_131_ = lean_string_append(v___x_129_, v___x_130_);
v___x_132_ = lean_string_append(v___x_131_, v___y_122_);
lean_dec_ref(v___y_122_);
v_str_102_ = v___x_132_;
goto v___jp_101_;
}
v___jp_133_:
{
if (lean_obj_tag(v_reportPos_x3f_86_) == 1)
{
if (lean_obj_tag(v_endPos_115_) == 0)
{
lean_object* v_val_135_; lean_object* v___x_136_; 
v_val_135_ = lean_ctor_get(v_reportPos_x3f_86_, 0);
v___x_136_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_121_ = v_val_135_;
v___y_122_ = v_str_134_;
v___y_123_ = v___x_136_;
goto v___jp_120_;
}
else
{
lean_object* v_val_137_; lean_object* v_val_138_; lean_object* v_line_139_; lean_object* v_column_140_; lean_object* v_line_141_; uint8_t v___x_142_; 
v_val_137_ = lean_ctor_get(v_endPos_115_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v_endPos_115_);
v_val_138_ = lean_ctor_get(v_reportPos_x3f_86_, 0);
v_line_139_ = lean_ctor_get(v_val_137_, 0);
v_column_140_ = lean_ctor_get(v_val_137_, 1);
v_line_141_ = lean_ctor_get(v_pos_114_, 0);
v___x_142_ = lean_nat_dec_eq(v_line_139_, v_line_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_138_, v_val_137_);
v___y_121_ = v_val_138_;
v___y_122_ = v_str_134_;
v___y_123_ = v___x_143_;
goto v___jp_120_;
}
else
{
lean_object* v___x_144_; 
lean_inc(v_column_140_);
lean_dec(v_val_137_);
v___x_144_ = l_Nat_reprFast(v_column_140_);
v___y_121_ = v_val_138_;
v___y_122_ = v_str_134_;
v___y_123_ = v___x_144_;
goto v___jp_120_;
}
}
}
else
{
lean_dec(v_endPos_115_);
lean_dec_ref(v_pos_114_);
v_str_102_ = v_str_134_;
goto v___jp_101_;
}
}
v___jp_145_:
{
uint8_t v___x_147_; 
v___x_147_ = l_Lean_Message_isTrace(v_msg_85_);
lean_dec_ref(v_msg_85_);
if (v___x_147_ == 0)
{
switch(v_severity_116_)
{
case 0:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4));
v___x_149_ = lean_string_append(v___x_148_, v_str_146_);
lean_dec_ref(v_str_146_);
v_str_134_ = v___x_149_;
goto v___jp_133_;
}
case 1:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5));
v___x_151_ = lean_string_append(v___x_150_, v_str_146_);
lean_dec_ref(v_str_146_);
v_str_134_ = v___x_151_;
goto v___jp_133_;
}
default: 
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6));
v___x_153_ = lean_string_append(v___x_152_, v_str_146_);
lean_dec_ref(v_str_146_);
v_str_134_ = v___x_153_;
goto v___jp_133_;
}
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7));
v___x_155_ = lean_string_append(v___x_154_, v_str_146_);
lean_dec_ref(v_str_146_);
v_str_134_ = v___x_155_;
goto v___jp_133_;
}
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_159_ = lean_string_append(v___x_158_, v___y_157_);
lean_dec_ref(v___y_157_);
v_str_146_ = v___x_159_;
goto v___jp_145_;
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_163_ = lean_string_utf8_byte_size(v_str_161_);
v___x_164_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_165_ = lean_nat_dec_le(v___x_164_, v___x_163_);
if (v___x_165_ == 0)
{
v___y_157_ = v_str_161_;
goto v___jp_156_;
}
else
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_string_memcmp(v_str_161_, v___x_162_, v___x_166_, v___x_166_, v___x_164_);
if (v___x_167_ == 0)
{
v___y_157_ = v_str_161_;
goto v___jp_156_;
}
else
{
v_str_146_ = v_str_161_;
goto v___jp_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object* v_msg_173_, lean_object* v_reportPos_x3f_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_173_, v_reportPos_x3f_174_);
lean_dec(v_reportPos_x3f_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(uint8_t v_x_177_){
_start:
{
switch(v_x_177_)
{
case 0:
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
return v___x_178_;
}
case 1:
{
lean_object* v___x_179_; 
v___x_179_ = lean_unsigned_to_nat(1u);
return v___x_179_;
}
default: 
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(2u);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___boxed(lean_object* v_x_181_){
_start:
{
uint8_t v_x_boxed_182_; lean_object* v_res_183_; 
v_x_boxed_182_ = lean_unbox(v_x_181_);
v_res_183_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_boxed_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(uint8_t v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx___boxed(lean_object* v_x_186_){
_start:
{
uint8_t v_x_4__boxed_187_; lean_object* v_res_188_; 
v_x_4__boxed_187_ = lean_unbox(v_x_186_);
v_res_188_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(v_x_4__boxed_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_189_){
_start:
{
lean_inc(v_k_189_);
return v_k_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_190_);
lean_dec(v_k_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_192_, lean_object* v_ctorIdx_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_k_196_){
_start:
{
lean_inc(v_k_196_);
return v_k_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_197_, lean_object* v_ctorIdx_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_k_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_197_, v_ctorIdx_198_, v_t_boxed_202_, v_h_200_, v_k_201_);
lean_dec(v_k_201_);
lean_dec(v_ctorIdx_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_204_){
_start:
{
lean_inc(v_check_204_);
return v_check_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_205_);
lean_dec(v_check_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_check_210_){
_start:
{
lean_inc(v_check_210_);
return v_check_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_check_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_check_214_);
lean_dec(v_check_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_217_){
_start:
{
lean_inc(v_drop_217_);
return v_drop_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_218_);
lean_dec(v_drop_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_drop_223_){
_start:
{
lean_inc(v_drop_223_);
return v_drop_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_drop_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_drop_227_);
lean_dec(v_drop_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_230_){
_start:
{
lean_inc(v_pass_230_);
return v_pass_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_231_);
lean_dec(v_pass_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_pass_236_){
_start:
{
lean_inc(v_pass_236_);
return v_pass_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_pass_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_pass_240_);
lean_dec(v_pass_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t v_x_243_){
_start:
{
switch(v_x_243_)
{
case 0:
{
lean_object* v___x_244_; 
v___x_244_ = lean_unsigned_to_nat(0u);
return v___x_244_;
}
case 1:
{
lean_object* v___x_245_; 
v___x_245_ = lean_unsigned_to_nat(1u);
return v___x_245_;
}
default: 
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(2u);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object* v_x_247_){
_start:
{
uint8_t v_x_boxed_248_; lean_object* v_res_249_; 
v_x_boxed_248_ = lean_unbox(v_x_247_);
v_res_249_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_boxed_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(uint8_t v_x_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx___boxed(lean_object* v_x_252_){
_start:
{
uint8_t v_x_4__boxed_253_; lean_object* v_res_254_; 
v_x_4__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(v_x_4__boxed_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_255_){
_start:
{
lean_inc(v_k_255_);
return v_k_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_256_);
lean_dec(v_k_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_258_, lean_object* v_ctorIdx_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_k_262_){
_start:
{
lean_inc(v_k_262_);
return v_k_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_263_, lean_object* v_ctorIdx_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_k_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_263_, v_ctorIdx_264_, v_t_boxed_268_, v_h_266_, v_k_267_);
lean_dec(v_k_267_);
lean_dec(v_ctorIdx_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_270_){
_start:
{
lean_inc(v_exact_270_);
return v_exact_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_271_);
lean_dec(v_exact_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_exact_276_){
_start:
{
lean_inc(v_exact_276_);
return v_exact_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_exact_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_exact_280_);
lean_dec(v_exact_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_283_){
_start:
{
lean_inc(v_normalized_283_);
return v_normalized_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_284_);
lean_dec(v_normalized_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_normalized_289_){
_start:
{
lean_inc(v_normalized_289_);
return v_normalized_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_normalized_293_){
_start:
{
uint8_t v_t_boxed_294_; lean_object* v_res_295_; 
v_t_boxed_294_ = lean_unbox(v_t_291_);
v_res_295_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_normalized_293_);
lean_dec(v_normalized_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_296_){
_start:
{
lean_inc(v_lax_296_);
return v_lax_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_297_);
lean_dec(v_lax_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_299_, uint8_t v_t_300_, lean_object* v_h_301_, lean_object* v_lax_302_){
_start:
{
lean_inc(v_lax_302_);
return v_lax_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_lax_306_){
_start:
{
uint8_t v_t_boxed_307_; lean_object* v_res_308_; 
v_t_boxed_307_ = lean_unbox(v_t_304_);
v_res_308_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_303_, v_t_boxed_307_, v_h_305_, v_lax_306_);
lean_dec(v_lax_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t v_x_309_){
_start:
{
if (v_x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_unsigned_to_nat(0u);
return v___x_310_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = lean_unsigned_to_nat(1u);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object* v_x_312_){
_start:
{
uint8_t v_x_boxed_313_; lean_object* v_res_314_; 
v_x_boxed_313_ = lean_unbox(v_x_312_);
v_res_314_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_boxed_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(uint8_t v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx___boxed(lean_object* v_x_317_){
_start:
{
uint8_t v_x_4__boxed_318_; lean_object* v_res_319_; 
v_x_4__boxed_318_ = lean_unbox(v_x_317_);
v_res_319_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(v_x_4__boxed_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_320_){
_start:
{
lean_inc(v_k_320_);
return v_k_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_321_);
lean_dec(v_k_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_323_, lean_object* v_ctorIdx_324_, uint8_t v_t_325_, lean_object* v_h_326_, lean_object* v_k_327_){
_start:
{
lean_inc(v_k_327_);
return v_k_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_328_, lean_object* v_ctorIdx_329_, lean_object* v_t_330_, lean_object* v_h_331_, lean_object* v_k_332_){
_start:
{
uint8_t v_t_boxed_333_; lean_object* v_res_334_; 
v_t_boxed_333_ = lean_unbox(v_t_330_);
v_res_334_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_328_, v_ctorIdx_329_, v_t_boxed_333_, v_h_331_, v_k_332_);
lean_dec(v_k_332_);
lean_dec(v_ctorIdx_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_335_){
_start:
{
lean_inc(v_exact_335_);
return v_exact_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_336_);
lean_dec(v_exact_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_338_, uint8_t v_t_339_, lean_object* v_h_340_, lean_object* v_exact_341_){
_start:
{
lean_inc(v_exact_341_);
return v_exact_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_342_, lean_object* v_t_343_, lean_object* v_h_344_, lean_object* v_exact_345_){
_start:
{
uint8_t v_t_boxed_346_; lean_object* v_res_347_; 
v_t_boxed_346_ = lean_unbox(v_t_343_);
v_res_347_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_342_, v_t_boxed_346_, v_h_344_, v_exact_345_);
lean_dec(v_exact_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_348_){
_start:
{
lean_inc(v_sorted_348_);
return v_sorted_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_349_);
lean_dec(v_sorted_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_351_, uint8_t v_t_352_, lean_object* v_h_353_, lean_object* v_sorted_354_){
_start:
{
lean_inc(v_sorted_354_);
return v_sorted_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_sorted_358_){
_start:
{
uint8_t v_t_boxed_359_; lean_object* v_res_360_; 
v_t_boxed_359_ = lean_unbox(v_t_356_);
v_res_360_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_355_, v_t_boxed_359_, v_h_357_, v_sorted_358_);
lean_dec(v_sorted_358_);
return v_res_360_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_box(0);
v___x_362_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
if (lean_obj_tag(v_action_x3f_397_) == 1)
{
lean_object* v_val_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_432_; 
v_val_401_ = lean_ctor_get(v_action_x3f_397_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_action_x3f_397_);
if (v_isSharedCheck_432_ == 0)
{
v___x_403_ = v_action_x3f_397_;
v_isShared_404_ = v_isSharedCheck_432_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_val_401_);
lean_dec(v_action_x3f_397_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_432_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2));
lean_inc(v_val_401_);
v___x_406_ = l_Lean_Syntax_isOfKind(v_val_401_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
lean_del_object(v___x_403_);
lean_dec(v_val_401_);
v___x_407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_Syntax_getArg(v_val_401_, v___x_408_);
lean_dec(v_val_401_);
v___x_410_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5));
lean_inc(v___x_409_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7));
lean_inc(v___x_409_);
v___x_413_ = l_Lean_Syntax_isOfKind(v___x_409_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9));
v___x_415_ = l_Lean_Syntax_isOfKind(v___x_409_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_del_object(v___x_403_);
v___x_416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_416_;
}
else
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_417_ = 2;
v___x_418_ = lean_box(v___x_417_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_418_);
v___x_420_ = v___x_403_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v___x_409_);
v___x_422_ = 1;
v___x_423_ = lean_box(v___x_422_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_423_);
v___x_425_ = v___x_403_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec(v___x_409_);
v___x_427_ = 0;
v___x_428_ = lean_box(v___x_427_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_428_);
v___x_430_ = v___x_403_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
else
{
uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_action_x3f_397_);
v___x_433_ = 0;
v___x_434_ = lean_box(v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_440_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_441_, lean_object* v_x_442_){
_start:
{
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_443_, lean_object* v_x_444_){
_start:
{
uint8_t v___x_1582__boxed_445_; uint8_t v_res_446_; lean_object* v_r_447_; 
v___x_1582__boxed_445_ = lean_unbox(v___x_443_);
v_res_446_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_1582__boxed_445_, v_x_444_);
lean_dec_ref(v_x_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_448_, lean_object* v_msg_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = l_Lean_Message_isTrace(v_msg_449_);
if (v___x_450_ == 0)
{
uint8_t v_severity_451_; uint8_t v___x_452_; uint8_t v___x_453_; 
v_severity_451_ = lean_ctor_get_uint8(v_msg_449_, sizeof(void*)*5 + 1);
v___x_452_ = 2;
v___x_453_ = l_Lean_instBEqMessageSeverity_beq(v_severity_451_, v___x_452_);
return v___x_453_;
}
else
{
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_454_, lean_object* v_msg_455_){
_start:
{
uint8_t v___x_1588__boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v___x_1588__boxed_456_ = lean_unbox(v___x_454_);
v_res_457_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_1588__boxed_456_, v_msg_455_);
lean_dec_ref(v_msg_455_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_459_, lean_object* v_msg_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_Message_isTrace(v_msg_460_);
if (v___x_461_ == 0)
{
uint8_t v_severity_462_; uint8_t v___x_463_; uint8_t v___x_464_; 
v_severity_462_ = lean_ctor_get_uint8(v_msg_460_, sizeof(void*)*5 + 1);
v___x_463_ = 1;
v___x_464_ = l_Lean_instBEqMessageSeverity_beq(v_severity_462_, v___x_463_);
return v___x_464_;
}
else
{
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_465_, lean_object* v_msg_466_){
_start:
{
uint8_t v___x_1597__boxed_467_; uint8_t v_res_468_; lean_object* v_r_469_; 
v___x_1597__boxed_467_ = lean_unbox(v___x_465_);
v_res_468_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_1597__boxed_467_, v_msg_466_);
lean_dec_ref(v_msg_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_470_, lean_object* v_msg_471_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_Message_isTrace(v_msg_471_);
if (v___x_472_ == 0)
{
uint8_t v_severity_473_; uint8_t v___x_474_; uint8_t v___x_475_; 
v_severity_473_ = lean_ctor_get_uint8(v_msg_471_, sizeof(void*)*5 + 1);
v___x_474_ = 0;
v___x_475_ = l_Lean_instBEqMessageSeverity_beq(v_severity_473_, v___x_474_);
return v___x_475_;
}
else
{
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_476_, lean_object* v_msg_477_){
_start:
{
uint8_t v___x_1606__boxed_478_; uint8_t v_res_479_; lean_object* v_r_480_; 
v___x_1606__boxed_478_ = lean_unbox(v___x_476_);
v_res_479_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_1606__boxed_478_, v_msg_477_);
lean_dec_ref(v_msg_477_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_506_){
_start:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_506_);
v___x_509_ = l_Lean_Syntax_isOfKind(v_x_506_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v_x_506_);
v___x_510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = l_Lean_Syntax_getArg(v_x_506_, v___x_511_);
lean_dec(v_x_506_);
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_512_);
v___x_514_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_512_);
v___x_516_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_512_);
v___x_518_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_512_);
v___x_520_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_522_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___f_525_; lean_object* v___x_526_; 
v___x_524_ = lean_box(v___x_522_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_525_, 0, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___f_525_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___f_528_; lean_object* v___x_529_; 
lean_dec(v___x_512_);
v___x_527_ = lean_box(v___x_518_);
v___f_528_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_528_, 0, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___f_528_);
return v___x_529_;
}
}
else
{
lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
lean_dec(v___x_512_);
v___x_530_ = lean_box(v___x_516_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___f_531_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
lean_dec(v___x_512_);
v___x_533_ = lean_box(v___x_514_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_534_, 0, v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___f_534_);
return v___x_535_;
}
}
else
{
lean_object* v___f_536_; lean_object* v___x_537_; 
lean_dec(v___x_512_);
v___f_536_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___f_536_);
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_541_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
return v_res_550_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_551_){
_start:
{
uint8_t v___x_552_; 
v___x_552_ = 0;
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_553_);
lean_dec_ref(v_x_553_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_556_, lean_object* v___y_557_){
_start:
{
if (lean_obj_tag(v_snd_556_) == 0)
{
uint8_t v___x_558_; 
lean_dec_ref(v___y_557_);
v___x_558_ = 0;
return v___x_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_val_559_ = lean_ctor_get(v_snd_556_, 0);
lean_inc(v_val_559_);
lean_dec_ref(v_snd_556_);
v___x_560_ = lean_apply_1(v_val_559_, v___y_557_);
v___x_561_ = lean_unbox(v___x_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_562_, lean_object* v___y_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_562_, v___y_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_566_, lean_object* v_snd_567_, uint8_t v_a_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
lean_inc_ref(v___y_569_);
v___x_570_ = lean_apply_1(v_a_566_, v___y_569_);
v___x_571_ = lean_unbox(v___x_570_);
if (v___x_571_ == 0)
{
if (lean_obj_tag(v_snd_567_) == 0)
{
uint8_t v___x_572_; 
lean_dec_ref(v___y_569_);
v___x_572_ = 2;
return v___x_572_;
}
else
{
lean_object* v_val_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_val_573_ = lean_ctor_get(v_snd_567_, 0);
lean_inc(v_val_573_);
lean_dec_ref(v_snd_567_);
v___x_574_ = lean_apply_1(v_val_573_, v___y_569_);
v___x_575_ = lean_unbox(v___x_574_);
return v___x_575_;
}
}
else
{
lean_dec_ref(v___y_569_);
lean_dec(v_snd_567_);
return v_a_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_576_, lean_object* v_snd_577_, lean_object* v_a_578_, lean_object* v___y_579_){
_start:
{
uint8_t v_a_11567__boxed_580_; uint8_t v_res_581_; lean_object* v_r_582_; 
v_a_11567__boxed_580_ = lean_unbox(v_a_578_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_576_, v_snd_577_, v_a_11567__boxed_580_, v___y_579_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_643_, size_t v_sz_644_, size_t v_i_645_, lean_object* v_b_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_a_651_; uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_645_, v_sz_644_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_b_646_);
return v___x_656_;
}
else
{
lean_object* v_snd_657_; lean_object* v_snd_658_; lean_object* v_snd_659_; lean_object* v_fst_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_967_; 
v_snd_657_ = lean_ctor_get(v_b_646_, 1);
lean_inc(v_snd_657_);
v_snd_658_ = lean_ctor_get(v_snd_657_, 1);
lean_inc(v_snd_658_);
v_snd_659_ = lean_ctor_get(v_snd_658_, 1);
lean_inc(v_snd_659_);
v_fst_660_ = lean_ctor_get(v_b_646_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_b_646_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_b_646_, 1);
lean_dec(v_unused_968_);
v___x_662_ = v_b_646_;
v_isShared_663_ = v_isSharedCheck_967_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_fst_660_);
lean_dec(v_b_646_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_967_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_fst_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_965_; 
v_fst_664_ = lean_ctor_get(v_snd_657_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_snd_657_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_snd_657_, 1);
lean_dec(v_unused_966_);
v___x_666_ = v_snd_657_;
v_isShared_667_ = v_isSharedCheck_965_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_fst_664_);
lean_dec(v_snd_657_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_965_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_963_; 
v_fst_668_ = lean_ctor_get(v_snd_658_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_snd_658_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_snd_658_, 1);
lean_dec(v_unused_964_);
v___x_670_ = v_snd_658_;
v_isShared_671_ = v_isSharedCheck_963_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_fst_668_);
lean_dec(v_snd_658_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_963_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_962_; 
v_fst_672_ = lean_ctor_get(v_snd_659_, 0);
v_snd_673_ = lean_ctor_get(v_snd_659_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_snd_659_);
if (v_isSharedCheck_962_ == 0)
{
v___x_675_ = v_snd_659_;
v_isShared_676_ = v_isSharedCheck_962_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snd_673_);
lean_inc(v_fst_672_);
lean_dec(v_snd_659_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_962_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_a_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_a_677_ = lean_array_uget_borrowed(v_as_643_, v_i_645_);
v___x_678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_677_);
v___x_679_ = l_Lean_Syntax_isOfKind(v_a_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v___x_680_);
if (v_isShared_676_ == 0)
{
v___x_682_ = v___x_675_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_672_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_snd_673_);
v___x_682_ = v_reuseFailAlloc_692_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_682_);
v___x_684_ = v___x_670_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_691_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_684_);
v___x_686_ = v___x_666_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_fst_664_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_688_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_686_);
v___x_688_ = v___x_662_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_660_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_a_651_ = v___x_688_;
goto v___jp_650_;
}
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_675_);
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_del_object(v___x_670_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
v_a_693_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_680_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_680_);
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
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_action_x3f_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = l_Lean_Syntax_getArg(v_a_677_, v___x_701_);
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_702_);
v___x_744_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
lean_del_object(v___x_675_);
lean_del_object(v___x_670_);
lean_del_object(v___x_666_);
lean_del_object(v___x_662_);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_702_);
v___x_746_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; uint8_t v_reportPositions_748_; 
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_702_);
v_reportPositions_748_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_747_);
if (v_reportPositions_748_ == 0)
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_702_);
v___x_750_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_702_);
v___x_752_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v___x_702_);
v___x_753_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref(v___x_753_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_fst_672_);
lean_ctor_set(v___x_754_, 1, v_snd_673_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_fst_668_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_fst_664_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_fst_660_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v_a_651_ = v___x_757_;
goto v___jp_650_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_758_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_753_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_766_ = lean_unsigned_to_nat(2u);
v___x_767_ = l_Lean_Syntax_getArg(v___x_702_, v___x_766_);
lean_dec(v___x_702_);
v___x_768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_767_);
v___x_769_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_771_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v___x_772_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_fst_672_);
lean_ctor_set(v___x_773_, 1, v_snd_673_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_fst_668_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_fst_664_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_fst_660_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v_a_651_ = v___x_776_;
goto v___jp_650_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_777_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_772_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_772_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec(v_fst_672_);
v___x_785_ = lean_box(v_reportPositions_748_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_snd_673_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_668_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_fst_664_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_660_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v_a_651_ = v___x_789_;
goto v___jp_650_;
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v___x_767_);
lean_dec(v_fst_672_);
v___x_790_ = lean_box(v___x_679_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_snd_673_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_fst_668_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_fst_664_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_fst_660_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v_a_651_ = v___x_794_;
goto v___jp_650_;
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_795_ = lean_unsigned_to_nat(2u);
v___x_796_ = l_Lean_Syntax_getArg(v___x_702_, v___x_795_);
lean_dec(v___x_702_);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_796_);
v___x_798_ = l_Lean_Syntax_isOfKind(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec(v___x_796_);
v___x_799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v___x_799_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_672_);
lean_ctor_set(v___x_800_, 1, v_snd_673_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_fst_668_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_fst_664_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_fst_660_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v_a_651_ = v___x_803_;
goto v___jp_650_;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_804_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_799_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_799_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = l_Lean_Syntax_getArg(v___x_796_, v___x_701_);
lean_dec(v___x_796_);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_812_);
v___x_814_ = l_Lean_Syntax_isOfKind(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_816_ = l_Lean_Syntax_isOfKind(v___x_812_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref(v___x_817_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_fst_672_);
lean_ctor_set(v___x_818_, 1, v_snd_673_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_fst_668_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_fst_664_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_fst_660_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v_a_651_ = v___x_821_;
goto v___jp_650_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_822_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_817_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_817_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_fst_668_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_fst_672_);
lean_ctor_set(v___x_830_, 1, v_snd_673_);
v___x_831_ = lean_box(v_reportPositions_748_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_fst_664_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_fst_660_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v_a_651_ = v___x_834_;
goto v___jp_650_;
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v___x_812_);
lean_dec(v_fst_668_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_fst_672_);
lean_ctor_set(v___x_835_, 1, v_snd_673_);
v___x_836_ = lean_box(v___x_679_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_fst_664_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_fst_660_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v_a_651_ = v___x_839_;
goto v___jp_650_;
}
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_840_ = lean_unsigned_to_nat(2u);
v___x_841_ = l_Lean_Syntax_getArg(v___x_702_, v___x_840_);
lean_dec(v___x_702_);
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_841_);
v___x_843_ = l_Lean_Syntax_isOfKind(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v___x_841_);
v___x_844_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___x_844_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_fst_672_);
lean_ctor_set(v___x_845_, 1, v_snd_673_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_fst_668_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_fst_664_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_fst_660_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v_a_651_ = v___x_848_;
goto v___jp_650_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_849_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_844_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_844_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = l_Lean_Syntax_getArg(v___x_841_, v___x_701_);
lean_dec(v___x_841_);
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_857_);
v___x_859_ = l_Lean_Syntax_isOfKind(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_861_ = l_Lean_Syntax_isOfKind(v___x_857_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v___x_862_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_fst_672_);
lean_ctor_set(v___x_863_, 1, v_snd_673_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_fst_668_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_fst_664_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_fst_660_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v_a_651_ = v___x_866_;
goto v___jp_650_;
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_867_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_862_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_862_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v_fst_664_);
v___x_875_ = 1;
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_fst_672_);
lean_ctor_set(v___x_876_, 1, v_snd_673_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_fst_668_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_box(v___x_875_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___x_877_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_fst_660_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v_a_651_ = v___x_880_;
goto v___jp_650_;
}
}
else
{
uint8_t v_ordering_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v___x_857_);
lean_dec(v_fst_664_);
v_ordering_881_ = 0;
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_fst_672_);
lean_ctor_set(v___x_882_, 1, v_snd_673_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_fst_668_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_box(v_ordering_881_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_fst_660_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v_a_651_ = v___x_886_;
goto v___jp_650_;
}
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_887_ = lean_unsigned_to_nat(2u);
v___x_888_ = l_Lean_Syntax_getArg(v___x_702_, v___x_887_);
lean_dec(v___x_702_);
v___x_889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_888_);
v___x_890_ = l_Lean_Syntax_isOfKind(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v___x_888_);
v___x_891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v___x_891_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_fst_672_);
lean_ctor_set(v___x_892_, 1, v_snd_673_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_fst_668_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_fst_664_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_fst_660_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v_a_651_ = v___x_895_;
goto v___jp_650_;
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_896_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_891_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_904_ = l_Lean_Syntax_getArg(v___x_888_, v___x_701_);
lean_dec(v___x_888_);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_904_);
v___x_906_ = l_Lean_Syntax_isOfKind(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_904_);
v___x_908_ = l_Lean_Syntax_isOfKind(v___x_904_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_910_ = l_Lean_Syntax_isOfKind(v___x_904_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref(v___x_911_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_fst_672_);
lean_ctor_set(v___x_912_, 1, v_snd_673_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_fst_668_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_fst_664_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_fst_660_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v_a_651_ = v___x_915_;
goto v___jp_650_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_916_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_911_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v_fst_660_);
v___x_924_ = 2;
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_fst_672_);
lean_ctor_set(v___x_925_, 1, v_snd_673_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_fst_668_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_664_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_box(v___x_924_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
v_a_651_ = v___x_929_;
goto v___jp_650_;
}
}
else
{
uint8_t v_whitespace_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v___x_904_);
lean_dec(v_fst_660_);
v_whitespace_930_ = 1;
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_fst_672_);
lean_ctor_set(v___x_931_, 1, v_snd_673_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_fst_668_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_fst_664_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_box(v_whitespace_930_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
v_a_651_ = v___x_935_;
goto v___jp_650_;
}
}
else
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec(v___x_904_);
lean_dec(v_fst_660_);
v___x_936_ = 0;
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_fst_672_);
lean_ctor_set(v___x_937_, 1, v_snd_673_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_fst_668_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_fst_664_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_box(v___x_936_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
v_a_651_ = v___x_941_;
goto v___jp_650_;
}
}
}
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = l_Lean_Syntax_getArg(v___x_702_, v___x_701_);
v___x_943_ = l_Lean_Syntax_isNone(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_942_);
v___x_945_ = l_Lean_Syntax_matchesNull(v___x_942_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
lean_dec(v___x_942_);
lean_dec(v___x_702_);
lean_del_object(v___x_675_);
lean_del_object(v___x_670_);
lean_del_object(v___x_666_);
lean_del_object(v___x_662_);
v___x_946_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v___x_946_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_fst_672_);
lean_ctor_set(v___x_947_, 1, v_snd_673_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_fst_668_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_fst_664_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_fst_660_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v_a_651_ = v___x_950_;
goto v___jp_650_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
v_a_951_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_946_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_946_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = l_Lean_Syntax_getArg(v___x_942_, v___x_701_);
lean_dec(v___x_942_);
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
v_action_x3f_704_ = v___x_960_;
v___y_705_ = v___y_647_;
v___y_706_ = v___y_648_;
goto v___jp_703_;
}
}
else
{
lean_object* v___x_961_; 
lean_dec(v___x_942_);
v___x_961_ = lean_box(0);
v_action_x3f_704_ = v___x_961_;
v___y_705_ = v___y_647_;
v___y_706_ = v___y_648_;
goto v___jp_703_;
}
}
v___jp_703_:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = l_Lean_Syntax_getArg(v___x_702_, v___x_709_);
lean_dec(v___x_702_);
v___x_711_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_713_, 0, v_a_712_);
lean_closure_set(v___f_713_, 1, v_snd_673_);
lean_closure_set(v___f_713_, 2, v_a_708_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___f_713_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_714_);
v___x_716_ = v___x_675_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_fst_672_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_726_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_716_);
v___x_718_ = v___x_670_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_725_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_718_);
v___x_720_ = v___x_666_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_664_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_720_);
v___x_722_ = v___x_662_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_660_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v_a_651_ = v___x_722_;
goto v___jp_650_;
}
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_708_);
lean_del_object(v___x_675_);
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_del_object(v___x_670_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
v_a_727_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_711_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_711_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v___x_702_);
lean_del_object(v___x_675_);
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_del_object(v___x_670_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
v_a_735_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_707_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_707_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
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
v___jp_650_:
{
size_t v___x_652_; size_t v___x_653_; 
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_add(v_i_645_, v___x_652_);
v_i_645_ = v___x_653_;
v_b_646_ = v_a_651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_969_, lean_object* v_sz_970_, lean_object* v_i_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
size_t v_sz_boxed_976_; size_t v_i_boxed_977_; lean_object* v_res_978_; 
v_sz_boxed_976_ = lean_unbox_usize(v_sz_970_);
lean_dec(v_sz_970_);
v_i_boxed_977_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_969_, v_sz_boxed_976_, v_i_boxed_977_, v_b_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_as_969_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_979_, size_t v_i_980_, lean_object* v_bs_981_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_bs_981_);
return v___x_983_;
}
else
{
lean_object* v_v_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_v_984_ = lean_array_uget(v_bs_981_, v_i_980_);
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_984_);
v___x_986_ = l_Lean_Syntax_isOfKind(v_v_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v_v_984_);
lean_dec_ref(v_bs_981_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v_bs_x27_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v_bs_x27_989_ = lean_array_uset(v_bs_981_, v_i_980_, v___x_988_);
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_980_, v___x_990_);
v___x_992_ = lean_array_uset(v_bs_x27_989_, v_i_980_, v_v_984_);
v_i_980_ = v___x_991_;
v_bs_981_ = v___x_992_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_994_, lean_object* v_i_995_, lean_object* v_bs_996_){
_start:
{
size_t v_sz_boxed_997_; size_t v_i_boxed_998_; lean_object* v_res_999_; 
v_sz_boxed_997_ = lean_unbox_usize(v_sz_994_);
lean_dec(v_sz_994_);
v_i_boxed_998_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_997_, v_i_boxed_998_, v_bs_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_1000_, lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_, lean_object* v_b_1004_){
_start:
{
lean_object* v___y_1006_; uint8_t v___x_1010_; 
v___x_1010_ = lean_usize_dec_eq(v_i_1002_, v_stop_1003_);
if (v___x_1010_ == 0)
{
lean_object* v_fst_1011_; uint8_t v___x_1012_; 
v_fst_1011_ = lean_ctor_get(v_b_1004_, 0);
v___x_1012_ = lean_unbox(v_fst_1011_);
if (v___x_1012_ == 0)
{
lean_object* v_snd_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
v_snd_1013_ = lean_ctor_get(v_b_1004_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_b_1004_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_b_1004_, 0);
lean_dec(v_unused_1022_);
v___x_1015_ = v_b_1004_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snd_1013_);
lean_dec(v_b_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(v___x_1000_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_snd_1013_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
v___y_1006_ = v___x_1019_;
goto v___jp_1005_;
}
}
}
else
{
lean_object* v_snd_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1033_; 
v_snd_1023_ = lean_ctor_get(v_b_1004_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_b_1004_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_b_1004_, 0);
lean_dec(v_unused_1034_);
v___x_1025_ = v_b_1004_;
v_isShared_1026_ = v_isSharedCheck_1033_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_snd_1023_);
lean_dec(v_b_1004_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1033_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1027_ = lean_array_uget_borrowed(v_as_1001_, v_i_1002_);
lean_inc(v___x_1027_);
v___x_1028_ = lean_array_push(v_snd_1023_, v___x_1027_);
v___x_1029_ = lean_box(v___x_1010_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___x_1028_);
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1028_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
v___y_1006_ = v___x_1031_;
goto v___jp_1005_;
}
}
}
}
else
{
return v_b_1004_;
}
v___jp_1005_:
{
size_t v___x_1007_; size_t v___x_1008_; 
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_1002_, v___x_1007_);
v_i_1002_ = v___x_1008_;
v_b_1004_ = v___y_1006_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1035_, lean_object* v_as_1036_, lean_object* v_i_1037_, lean_object* v_stop_1038_, lean_object* v_b_1039_){
_start:
{
uint8_t v___x_12442__boxed_1040_; size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; lean_object* v_res_1043_; 
v___x_12442__boxed_1040_ = lean_unbox(v___x_1035_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1038_);
lean_dec(v_stop_1038_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_12442__boxed_1040_, v_as_1036_, v_i_boxed_1041_, v_stop_boxed_1042_, v_b_1039_);
lean_dec_ref(v_as_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_elts_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1116_; lean_object* v_cfg_1130_; 
v_cfg_1130_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1072_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_val_1131_ = lean_ctor_get(v_spec_x3f_1072_, 0);
lean_inc(v_val_1131_);
lean_dec_ref(v_spec_x3f_1072_);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
lean_inc(v_val_1131_);
v___x_1133_ = l_Lean_Syntax_isOfKind(v_val_1131_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_val_1131_);
v___x_1134_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = l_Lean_Syntax_getArg(v_val_1131_, v___x_1143_);
lean_dec(v_val_1131_);
v___x_1145_ = l_Lean_Syntax_getArgs(v___x_1144_);
lean_dec(v___x_1144_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1148_ = lean_array_get_size(v___x_1145_);
v___x_1149_ = lean_nat_dec_lt(v___x_1146_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_dec_ref(v___x_1145_);
v___y_1116_ = v___x_1147_;
goto v___jp_1115_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_box(v___x_1133_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1147_);
v___x_1152_ = lean_nat_dec_le(v___x_1148_, v___x_1148_);
if (v___x_1152_ == 0)
{
if (v___x_1149_ == 0)
{
lean_dec_ref(v___x_1151_);
lean_dec_ref(v___x_1145_);
v___y_1116_ = v___x_1147_;
goto v___jp_1115_;
}
else
{
size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v_snd_1156_; 
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = lean_usize_of_nat(v___x_1148_);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1133_, v___x_1145_, v___x_1153_, v___x_1154_, v___x_1151_);
lean_dec_ref(v___x_1145_);
v_snd_1156_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_snd_1156_);
lean_dec_ref(v___x_1155_);
v___y_1116_ = v_snd_1156_;
goto v___jp_1115_;
}
}
else
{
size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; lean_object* v_snd_1160_; 
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1148_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1133_, v___x_1145_, v___x_1157_, v___x_1158_, v___x_1151_);
lean_dec_ref(v___x_1145_);
v_snd_1160_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_snd_1160_);
lean_dec_ref(v___x_1159_);
v___y_1116_ = v_snd_1160_;
goto v___jp_1115_;
}
}
}
}
else
{
lean_object* v___x_1161_; 
lean_dec(v_spec_x3f_1072_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_cfg_1130_);
return v___x_1161_;
}
v___jp_1076_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; size_t v_sz_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1080_ = l_Array_reverse___redArg(v_elts_1077_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1082_ = lean_array_size(v___x_1080_);
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1080_, v_sz_1082_, v___x_1083_, v___x_1081_, v___y_1078_, v___y_1079_);
lean_dec_ref(v___x_1080_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1106_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1106_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1106_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_snd_1089_; lean_object* v_snd_1090_; lean_object* v_snd_1091_; lean_object* v_fst_1092_; lean_object* v_fst_1093_; lean_object* v_fst_1094_; lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___y_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1104_; 
v_snd_1089_ = lean_ctor_get(v_a_1085_, 1);
lean_inc(v_snd_1089_);
v_snd_1090_ = lean_ctor_get(v_snd_1089_, 1);
lean_inc(v_snd_1090_);
v_snd_1091_ = lean_ctor_get(v_snd_1090_, 1);
lean_inc(v_snd_1091_);
v_fst_1092_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_fst_1092_);
lean_dec(v_a_1085_);
v_fst_1093_ = lean_ctor_get(v_snd_1089_, 0);
lean_inc(v_fst_1093_);
lean_dec(v_snd_1089_);
v_fst_1094_ = lean_ctor_get(v_snd_1090_, 0);
lean_inc(v_fst_1094_);
lean_dec(v_snd_1090_);
v_fst_1095_ = lean_ctor_get(v_snd_1091_, 0);
lean_inc(v_fst_1095_);
v_snd_1096_ = lean_ctor_get(v_snd_1091_, 1);
lean_inc(v_snd_1096_);
lean_dec(v_snd_1091_);
v___y_1097_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1097_, 0, v_snd_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1098_, 0, v___y_1097_);
v___x_1099_ = lean_unbox(v_fst_1092_);
lean_dec(v_fst_1092_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*1, v___x_1099_);
v___x_1100_ = lean_unbox(v_fst_1093_);
lean_dec(v_fst_1093_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*1 + 1, v___x_1100_);
v___x_1101_ = lean_unbox(v_fst_1094_);
lean_dec(v_fst_1094_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*1 + 2, v___x_1101_);
v___x_1102_ = lean_unbox(v_fst_1095_);
lean_dec(v_fst_1095_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*1 + 3, v___x_1102_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1098_);
v___x_1104_ = v___x_1087_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1098_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1084_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1084_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
v___jp_1115_:
{
size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v_sz_1117_ = lean_array_size(v___y_1116_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1117_, v___x_1118_, v___y_1116_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v___x_1120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_val_1129_; 
v_val_1129_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_val_1129_);
lean_dec_ref(v___x_1119_);
v_elts_1077_ = v_val_1129_;
v___y_1078_ = v_a_1073_;
v___y_1079_ = v_a_1074_;
goto v___jp_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1179_, lean_object* v_replacement_1180_, lean_object* v_a_1181_, lean_object* v_b_1182_){
_start:
{
lean_object* v_it_1184_; lean_object* v_startPos_1185_; lean_object* v_endPos_1186_; lean_object* v_it_1195_; 
switch(lean_obj_tag(v_a_1181_))
{
case 0:
{
lean_object* v_pos_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1213_; 
v_pos_1201_ = lean_ctor_get(v_a_1181_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1181_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1203_ = v_a_1181_;
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_pos_1201_);
lean_dec(v_a_1181_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_startInclusive_1205_; lean_object* v_endExclusive_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_startInclusive_1205_ = lean_ctor_get(v_s_1179_, 1);
v_endExclusive_1206_ = lean_ctor_get(v_s_1179_, 2);
v___x_1207_ = lean_nat_sub(v_endExclusive_1206_, v_startInclusive_1205_);
v___x_1208_ = lean_nat_dec_eq(v_pos_1201_, v___x_1207_);
lean_dec(v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1210_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_pos_1201_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
v_it_1195_ = v___x_1210_;
goto v___jp_1194_;
}
}
else
{
lean_object* v___x_1212_; 
lean_del_object(v___x_1203_);
lean_dec(v_pos_1201_);
v___x_1212_ = lean_box(3);
v_it_1195_ = v___x_1212_;
goto v___jp_1194_;
}
}
}
case 1:
{
lean_object* v_pos_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1226_; 
v_pos_1214_ = lean_ctor_get(v_a_1181_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_a_1181_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1216_ = v_a_1181_;
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_pos_1214_);
lean_dec(v_a_1181_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_str_1218_; lean_object* v_startInclusive_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v_str_1218_ = lean_ctor_get(v_s_1179_, 0);
v_startInclusive_1219_ = lean_ctor_get(v_s_1179_, 1);
v___x_1220_ = lean_nat_add(v_startInclusive_1219_, v_pos_1214_);
v___x_1221_ = lean_string_utf8_next_fast(v_str_1218_, v___x_1220_);
lean_dec(v___x_1220_);
v___x_1222_ = lean_nat_sub(v___x_1221_, v_startInclusive_1219_);
lean_inc(v___x_1222_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1222_);
v___x_1224_ = v___x_1216_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
v_it_1184_ = v___x_1224_;
v_startPos_1185_ = v_pos_1214_;
v_endPos_1186_ = v___x_1222_;
goto v___jp_1183_;
}
}
}
case 2:
{
lean_object* v_needle_1227_; lean_object* v_table_1228_; lean_object* v_stackPos_1229_; lean_object* v_needlePos_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1289_; 
v_needle_1227_ = lean_ctor_get(v_a_1181_, 0);
v_table_1228_ = lean_ctor_get(v_a_1181_, 1);
v_stackPos_1229_ = lean_ctor_get(v_a_1181_, 2);
v_needlePos_1230_ = lean_ctor_get(v_a_1181_, 3);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_a_1181_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1232_ = v_a_1181_;
v_isShared_1233_ = v_isSharedCheck_1289_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_needlePos_1230_);
lean_inc(v_stackPos_1229_);
lean_inc(v_table_1228_);
lean_inc(v_needle_1227_);
lean_dec(v_a_1181_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1289_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_str_1234_; lean_object* v_startInclusive_1235_; lean_object* v_endExclusive_1236_; lean_object* v_str_1237_; lean_object* v_startInclusive_1238_; lean_object* v_endExclusive_1239_; lean_object* v_basePos_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_str_1234_ = lean_ctor_get(v_needle_1227_, 0);
v_startInclusive_1235_ = lean_ctor_get(v_needle_1227_, 1);
v_endExclusive_1236_ = lean_ctor_get(v_needle_1227_, 2);
v_str_1237_ = lean_ctor_get(v_s_1179_, 0);
v_startInclusive_1238_ = lean_ctor_get(v_s_1179_, 1);
v_endExclusive_1239_ = lean_ctor_get(v_s_1179_, 2);
v_basePos_1240_ = lean_nat_sub(v_stackPos_1229_, v_needlePos_1230_);
v___x_1241_ = lean_nat_sub(v_endExclusive_1236_, v_startInclusive_1235_);
v___x_1242_ = lean_nat_add(v_basePos_1240_, v___x_1241_);
v___x_1243_ = lean_nat_sub(v_endExclusive_1239_, v_startInclusive_1238_);
v___x_1244_ = lean_nat_dec_le(v___x_1242_, v___x_1243_);
lean_dec(v___x_1242_);
if (v___x_1244_ == 0)
{
uint8_t v___x_1245_; 
lean_dec(v___x_1241_);
lean_del_object(v___x_1232_);
lean_dec(v_needlePos_1230_);
lean_dec(v_stackPos_1229_);
lean_dec_ref(v_table_1228_);
lean_dec_ref(v_needle_1227_);
v___x_1245_ = l_String_instDecidableLtRaw___aux__1(v_basePos_1240_, v___x_1243_);
if (v___x_1245_ == 0)
{
lean_dec(v___x_1243_);
lean_dec(v_basePos_1240_);
lean_dec_ref(v_s_1179_);
return v_b_1182_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = l_String_Slice_pos_x21(v_s_1179_, v_basePos_1240_);
lean_dec(v_basePos_1240_);
v___x_1247_ = lean_box(3);
v_it_1184_ = v___x_1247_;
v_startPos_1185_ = v___x_1246_;
v_endPos_1186_ = v___x_1243_;
goto v___jp_1183_;
}
}
else
{
lean_object* v___x_1248_; uint8_t v_stackByte_1249_; lean_object* v___x_1250_; uint8_t v_patByte_1251_; uint8_t v___x_1252_; 
lean_dec(v___x_1243_);
v___x_1248_ = lean_nat_add(v_startInclusive_1238_, v_stackPos_1229_);
v_stackByte_1249_ = lean_string_get_byte_fast(v_str_1237_, v___x_1248_);
v___x_1250_ = lean_nat_add(v_startInclusive_1235_, v_needlePos_1230_);
v_patByte_1251_ = lean_string_get_byte_fast(v_str_1234_, v___x_1250_);
v___x_1252_ = lean_uint8_dec_eq(v_stackByte_1249_, v_patByte_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
lean_dec(v___x_1241_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_nat_dec_eq(v_needlePos_1230_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_newNeedlePos_1257_; uint8_t v___x_1258_; 
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_nat_sub(v_needlePos_1230_, v___x_1255_);
lean_dec(v_needlePos_1230_);
v_newNeedlePos_1257_ = lean_array_fget_borrowed(v_table_1228_, v___x_1256_);
lean_dec(v___x_1256_);
v___x_1258_ = lean_nat_dec_eq(v_newNeedlePos_1257_, v___x_1253_);
if (v___x_1258_ == 0)
{
lean_object* v_oldBasePos_1259_; lean_object* v___x_1260_; lean_object* v_newBasePos_1261_; lean_object* v___x_1263_; 
lean_inc(v_newNeedlePos_1257_);
v_oldBasePos_1259_ = l_String_Slice_pos_x21(v_s_1179_, v_basePos_1240_);
lean_dec(v_basePos_1240_);
v___x_1260_ = lean_nat_sub(v_stackPos_1229_, v_newNeedlePos_1257_);
v_newBasePos_1261_ = l_String_Slice_pos_x21(v_s_1179_, v___x_1260_);
lean_dec(v___x_1260_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v_newNeedlePos_1257_);
v___x_1263_ = v___x_1232_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_needle_1227_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_table_1228_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_stackPos_1229_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_newNeedlePos_1257_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v_it_1184_ = v___x_1263_;
v_startPos_1185_ = v_oldBasePos_1259_;
v_endPos_1186_ = v_newBasePos_1261_;
goto v___jp_1183_;
}
}
else
{
lean_object* v_basePos_1265_; lean_object* v_nextStackPos_1266_; lean_object* v___x_1268_; 
v_basePos_1265_ = l_String_Slice_pos_x21(v_s_1179_, v_basePos_1240_);
lean_dec(v_basePos_1240_);
v_nextStackPos_1266_ = l_String_Slice_posGE___redArg(v_s_1179_, v_stackPos_1229_);
lean_inc(v_nextStackPos_1266_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v___x_1253_);
lean_ctor_set(v___x_1232_, 2, v_nextStackPos_1266_);
v___x_1268_ = v___x_1232_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_needle_1227_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_table_1228_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_nextStackPos_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v___x_1253_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v_it_1184_ = v___x_1268_;
v_startPos_1185_ = v_basePos_1265_;
v_endPos_1186_ = v_nextStackPos_1266_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v_basePos_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_nextStackPos_1273_; lean_object* v___x_1275_; 
lean_dec(v_basePos_1240_);
lean_dec(v_needlePos_1230_);
v_basePos_1270_ = l_String_Slice_pos_x21(v_s_1179_, v_stackPos_1229_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_stackPos_1229_, v___x_1271_);
lean_dec(v_stackPos_1229_);
v_nextStackPos_1273_ = l_String_Slice_posGE___redArg(v_s_1179_, v___x_1272_);
lean_inc(v_nextStackPos_1273_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v___x_1253_);
lean_ctor_set(v___x_1232_, 2, v_nextStackPos_1273_);
v___x_1275_ = v___x_1232_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_needle_1227_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_table_1228_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_nextStackPos_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___x_1253_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
v_it_1184_ = v___x_1275_;
v_startPos_1185_ = v_basePos_1270_;
v_endPos_1186_ = v_nextStackPos_1273_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v_nextStackPos_1278_; lean_object* v_nextNeedlePos_1279_; uint8_t v___x_1280_; 
lean_dec(v_basePos_1240_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1278_ = lean_nat_add(v_stackPos_1229_, v___x_1277_);
lean_dec(v_stackPos_1229_);
v_nextNeedlePos_1279_ = lean_nat_add(v_needlePos_1230_, v___x_1277_);
lean_dec(v_needlePos_1230_);
v___x_1280_ = lean_nat_dec_eq(v_nextNeedlePos_1279_, v___x_1241_);
lean_dec(v___x_1241_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1282_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v_nextNeedlePos_1279_);
lean_ctor_set(v___x_1232_, 2, v_nextStackPos_1278_);
v___x_1282_ = v___x_1232_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_needle_1227_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_table_1228_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_nextStackPos_1278_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_nextNeedlePos_1279_);
v___x_1282_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v_a_1181_ = v___x_1282_;
goto _start;
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_dec(v_nextNeedlePos_1279_);
v___x_1285_ = lean_unsigned_to_nat(0u);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v___x_1285_);
lean_ctor_set(v___x_1232_, 2, v_nextStackPos_1278_);
v___x_1287_ = v___x_1232_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_needle_1227_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_table_1228_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_nextStackPos_1278_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v_it_1195_ = v___x_1287_;
goto v___jp_1194_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1179_);
return v_b_1182_;
}
}
v___jp_1183_:
{
lean_object* v___x_1187_; lean_object* v_str_1188_; lean_object* v_startInclusive_1189_; lean_object* v_endExclusive_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_inc_ref(v_s_1179_);
v___x_1187_ = l_String_Slice_slice_x21(v_s_1179_, v_startPos_1185_, v_endPos_1186_);
lean_dec(v_endPos_1186_);
lean_dec(v_startPos_1185_);
v_str_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_str_1188_);
v_startInclusive_1189_ = lean_ctor_get(v___x_1187_, 1);
lean_inc(v_startInclusive_1189_);
v_endExclusive_1190_ = lean_ctor_get(v___x_1187_, 2);
lean_inc(v_endExclusive_1190_);
lean_dec_ref(v___x_1187_);
v___x_1191_ = lean_string_utf8_extract(v_str_1188_, v_startInclusive_1189_, v_endExclusive_1190_);
lean_dec(v_endExclusive_1190_);
lean_dec(v_startInclusive_1189_);
lean_dec_ref(v_str_1188_);
v___x_1192_ = lean_string_append(v_b_1182_, v___x_1191_);
lean_dec_ref(v___x_1191_);
v_a_1181_ = v_it_1184_;
v_b_1182_ = v___x_1192_;
goto _start;
}
v___jp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_string_utf8_byte_size(v_replacement_1180_);
v___x_1198_ = lean_string_utf8_extract(v_replacement_1180_, v___x_1196_, v___x_1197_);
v___x_1199_ = lean_string_append(v_b_1182_, v___x_1198_);
lean_dec_ref(v___x_1198_);
v_a_1181_ = v_it_1195_;
v_b_1182_ = v___x_1199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1290_, lean_object* v_replacement_1291_, lean_object* v_a_1292_, lean_object* v_b_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1290_, v_replacement_1291_, v_a_1292_, v_b_1293_);
lean_dec_ref(v_replacement_1291_);
return v_res_1294_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1297_ = lean_string_utf8_byte_size(v___x_1296_);
return v___x_1297_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1300_ = lean_nat_dec_eq(v___x_1299_, v___x_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1301_);
return v___x_1304_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1306_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4);
v___x_1309_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1310_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
lean_ctor_set(v___x_1310_, 2, v___x_1307_);
lean_ctor_set(v___x_1310_, 3, v___x_1307_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1313_, lean_object* v_replacement_1314_){
_start:
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1316_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5);
v___x_1318_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1313_, v_replacement_1314_, v___x_1317_, v___x_1315_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1320_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1313_, v_replacement_1314_, v___x_1319_, v___x_1315_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1321_, lean_object* v_replacement_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1321_, v_replacement_1322_);
lean_dec_ref(v_replacement_1322_);
return v_res_1323_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1326_ = lean_string_utf8_byte_size(v___x_1325_);
return v___x_1326_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1329_ = lean_nat_dec_eq(v___x_1328_, v___x_1327_);
return v___x_1329_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1331_);
lean_ctor_set(v___x_1333_, 2, v___x_1330_);
return v___x_1333_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1335_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4);
v___x_1338_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1339_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
lean_ctor_set(v___x_1339_, 2, v___x_1336_);
lean_ctor_set(v___x_1339_, 3, v___x_1336_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1340_, lean_object* v_replacement_1341_){
_start:
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1343_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5);
v___x_1345_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1340_, v_replacement_1341_, v___x_1344_, v___x_1342_);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1347_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1340_, v_replacement_1341_, v___x_1346_, v___x_1342_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1348_, lean_object* v_replacement_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1348_, v_replacement_1349_);
lean_dec_ref(v_replacement_1349_);
return v_res_1350_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1353_ = lean_string_utf8_byte_size(v___x_1352_);
return v___x_1353_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1356_ = lean_nat_dec_eq(v___x_1355_, v___x_1354_);
return v___x_1356_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
lean_ctor_set(v___x_1360_, 2, v___x_1357_);
return v___x_1360_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1362_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4);
v___x_1365_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1366_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1364_);
lean_ctor_set(v___x_1366_, 2, v___x_1363_);
lean_ctor_set(v___x_1366_, 3, v___x_1363_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1367_, lean_object* v_replacement_1368_){
_start:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1370_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5);
v___x_1372_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1367_, v_replacement_1368_, v___x_1371_, v___x_1369_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1374_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1367_, v_replacement_1368_, v___x_1373_, v___x_1369_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1375_, lean_object* v_replacement_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1375_, v_replacement_1376_);
lean_dec_ref(v_replacement_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_string_utf8_byte_size(v_s_1381_);
v___x_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1385_, 0, v_s_1381_);
lean_ctor_set(v___x_1385_, 1, v___x_1383_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v___x_1386_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1385_, v___x_1382_);
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1388_ = lean_string_utf8_byte_size(v___x_1386_);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1386_);
lean_ctor_set(v___x_1389_, 1, v___x_1383_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1389_, v___x_1387_);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1392_ = lean_string_utf8_byte_size(v___x_1390_);
v___x_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1390_);
lean_ctor_set(v___x_1393_, 1, v___x_1383_);
lean_ctor_set(v___x_1393_, 2, v___x_1392_);
v___x_1394_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1393_, v___x_1391_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1395_, lean_object* v_pattern_1396_, lean_object* v_replacement_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1395_, v_replacement_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1399_, lean_object* v_pattern_1400_, lean_object* v_replacement_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1399_, v_pattern_1400_, v_replacement_1401_);
lean_dec_ref(v_replacement_1401_);
lean_dec_ref(v_pattern_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1403_, lean_object* v_pattern_1404_, lean_object* v_replacement_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1403_, v_replacement_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1407_, lean_object* v_pattern_1408_, lean_object* v_replacement_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1407_, v_pattern_1408_, v_replacement_1409_);
lean_dec_ref(v_replacement_1409_);
lean_dec_ref(v_pattern_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1411_, lean_object* v_pattern_1412_, lean_object* v_replacement_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1411_, v_replacement_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1415_, lean_object* v_pattern_1416_, lean_object* v_replacement_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1415_, v_pattern_1416_, v_replacement_1417_);
lean_dec_ref(v_replacement_1417_);
lean_dec_ref(v_pattern_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1419_, lean_object* v_replacement_1420_, lean_object* v_inst_1421_, lean_object* v_R_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_, lean_object* v_c_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1419_, v_replacement_1420_, v_a_1423_, v_b_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1427_, lean_object* v_replacement_1428_, lean_object* v_inst_1429_, lean_object* v_R_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_, lean_object* v_c_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1427_, v_replacement_1428_, v_inst_1429_, v_R_1430_, v_a_1431_, v_b_1432_, v_c_1433_);
lean_dec_ref(v_replacement_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_string_utf8_byte_size(v_s_1435_);
v___x_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1439_, 0, v_s_1435_);
lean_ctor_set(v___x_1439_, 1, v___x_1437_);
lean_ctor_set(v___x_1439_, 2, v___x_1438_);
v___x_1440_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1439_, v___x_1436_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0));
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1445_);
lean_dec_ref(v_s_1445_);
return v_res_1446_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1449_ = lean_nat_dec_eq(v___x_1448_, v___x_1447_);
return v___x_1449_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1450_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v___x_1451_);
lean_ctor_set(v___x_1453_, 2, v___x_1450_);
return v___x_1453_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1455_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1454_);
return v___x_1455_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1458_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1459_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1457_);
lean_ctor_set(v___x_1459_, 2, v___x_1456_);
lean_ctor_set(v___x_1459_, 3, v___x_1456_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1460_, lean_object* v_replacement_1461_){
_start:
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1463_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1465_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1460_, v_replacement_1461_, v___x_1464_, v___x_1462_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1467_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1460_, v_replacement_1461_, v___x_1466_, v___x_1462_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1468_, lean_object* v_replacement_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1468_, v_replacement_1469_);
lean_dec_ref(v_replacement_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1471_, lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v_a_1474_, lean_object* v_b_1475_){
_start:
{
lean_object* v_it_1477_; lean_object* v_startInclusive_1478_; lean_object* v_endExclusive_1479_; 
if (lean_obj_tag(v_a_1474_) == 0)
{
lean_object* v_currPos_1487_; lean_object* v_searcher_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1523_; 
v_currPos_1487_ = lean_ctor_get(v_a_1474_, 0);
v_searcher_1488_ = lean_ctor_get(v_a_1474_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1490_ = v_a_1474_;
v_isShared_1491_ = v_isSharedCheck_1523_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_searcher_1488_);
lean_inc(v_currPos_1487_);
lean_dec(v_a_1474_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1523_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
uint8_t v___y_1503_; lean_object* v_startInclusive_1507_; lean_object* v_endExclusive_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_startInclusive_1507_ = lean_ctor_get(v___x_1472_, 1);
v_endExclusive_1508_ = lean_ctor_get(v___x_1472_, 2);
v___x_1509_ = lean_nat_sub(v_endExclusive_1508_, v_startInclusive_1507_);
v___x_1510_ = lean_nat_dec_eq(v_searcher_1488_, v___x_1509_);
lean_dec(v___x_1509_);
if (v___x_1510_ == 0)
{
uint32_t v___x_1511_; uint8_t v___y_1513_; uint32_t v___x_1518_; uint8_t v___x_1519_; 
v___x_1511_ = lean_string_utf8_get_fast(v_s_1471_, v_searcher_1488_);
v___x_1518_ = 32;
v___x_1519_ = lean_uint32_dec_eq(v___x_1511_, v___x_1518_);
if (v___x_1519_ == 0)
{
uint32_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = 9;
v___x_1521_ = lean_uint32_dec_eq(v___x_1511_, v___x_1520_);
v___y_1513_ = v___x_1521_;
goto v___jp_1512_;
}
else
{
v___y_1513_ = v___x_1519_;
goto v___jp_1512_;
}
v___jp_1512_:
{
if (v___y_1513_ == 0)
{
uint32_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = 13;
v___x_1515_ = lean_uint32_dec_eq(v___x_1511_, v___x_1514_);
if (v___x_1515_ == 0)
{
uint32_t v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = 10;
v___x_1517_ = lean_uint32_dec_eq(v___x_1511_, v___x_1516_);
v___y_1503_ = v___x_1517_;
goto v___jp_1502_;
}
else
{
v___y_1503_ = v___x_1515_;
goto v___jp_1502_;
}
}
else
{
goto v___jp_1492_;
}
}
}
else
{
lean_object* v___x_1522_; 
lean_del_object(v___x_1490_);
lean_dec(v_searcher_1488_);
v___x_1522_ = lean_box(1);
lean_inc(v___x_1473_);
v_it_1477_ = v___x_1522_;
v_startInclusive_1478_ = v_currPos_1487_;
v_endExclusive_1479_ = v___x_1473_;
goto v___jp_1476_;
}
v___jp_1492_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_slice_1496_; lean_object* v_nextIt_1498_; 
v___x_1493_ = lean_string_utf8_next_fast(v_s_1471_, v_searcher_1488_);
v___x_1494_ = lean_nat_sub(v___x_1493_, v_searcher_1488_);
v___x_1495_ = lean_nat_add(v_searcher_1488_, v___x_1494_);
lean_dec(v___x_1494_);
v_slice_1496_ = l_String_Slice_subslice_x21(v___x_1472_, v_currPos_1487_, v_searcher_1488_);
lean_inc(v___x_1495_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1495_);
lean_ctor_set(v___x_1490_, 0, v___x_1495_);
v_nextIt_1498_ = v___x_1490_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1495_);
v_nextIt_1498_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v_startInclusive_1499_; lean_object* v_endExclusive_1500_; 
v_startInclusive_1499_ = lean_ctor_get(v_slice_1496_, 0);
lean_inc(v_startInclusive_1499_);
v_endExclusive_1500_ = lean_ctor_get(v_slice_1496_, 1);
lean_inc(v_endExclusive_1500_);
lean_dec_ref(v_slice_1496_);
v_it_1477_ = v_nextIt_1498_;
v_startInclusive_1478_ = v_startInclusive_1499_;
v_endExclusive_1479_ = v_endExclusive_1500_;
goto v___jp_1476_;
}
}
v___jp_1502_:
{
if (v___y_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_del_object(v___x_1490_);
v___x_1504_ = lean_string_utf8_next_fast(v_s_1471_, v_searcher_1488_);
lean_dec(v_searcher_1488_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_currPos_1487_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v_a_1474_ = v___x_1505_;
goto _start;
}
else
{
goto v___jp_1492_;
}
}
}
}
else
{
lean_dec(v___x_1473_);
lean_dec_ref(v_s_1471_);
return v_b_1475_;
}
v___jp_1476_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_nat_sub(v_endExclusive_1479_, v_startInclusive_1478_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_nat_dec_eq(v___x_1480_, v___x_1481_);
lean_dec(v___x_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_inc_ref(v_s_1471_);
v___x_1483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1483_, 0, v_s_1471_);
lean_ctor_set(v___x_1483_, 1, v_startInclusive_1478_);
lean_ctor_set(v___x_1483_, 2, v_endExclusive_1479_);
v___x_1484_ = lean_array_push(v_b_1475_, v___x_1483_);
v_a_1474_ = v_it_1477_;
v_b_1475_ = v___x_1484_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1479_);
lean_dec(v_startInclusive_1478_);
v_a_1474_ = v_it_1477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1524_, lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_a_1527_, lean_object* v_b_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1524_, v___x_1525_, v___x_1526_, v_a_1527_, v_b_1528_);
lean_dec_ref(v___x_1525_);
return v_res_1529_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1531_ = lean_string_utf8_byte_size(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___x_1533_);
lean_ctor_set(v___x_1535_, 2, v___x_1532_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1538_, lean_object* v_s_1539_){
_start:
{
switch(v_mode_1538_)
{
case 0:
{
return v_s_1539_;
}
case 1:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = lean_string_utf8_byte_size(v_s_1539_);
v___x_1543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1543_, 0, v_s_1539_);
lean_ctor_set(v___x_1543_, 1, v___x_1541_);
lean_ctor_set(v___x_1543_, 2, v___x_1542_);
v___x_1544_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1543_, v___x_1540_);
return v___x_1544_;
}
default: 
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1);
v___x_1547_ = lean_string_utf8_byte_size(v_s_1539_);
lean_inc_ref(v_s_1539_);
v___x_1548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1548_, 0, v_s_1539_);
lean_ctor_set(v___x_1548_, 1, v___x_1545_);
lean_ctor_set(v___x_1548_, 2, v___x_1547_);
v___x_1549_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v___x_1548_);
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2));
v___x_1551_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1539_, v___x_1548_, v___x_1547_, v___x_1549_, v___x_1550_);
lean_dec_ref(v___x_1548_);
v___x_1552_ = lean_array_to_list(v___x_1551_);
v___x_1553_ = l_String_Slice_intercalate(v___x_1546_, v___x_1552_);
lean_dec(v___x_1552_);
return v___x_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1554_, lean_object* v_s_1555_){
_start:
{
uint8_t v_mode_boxed_1556_; lean_object* v_res_1557_; 
v_mode_boxed_1556_ = lean_unbox(v_mode_1554_);
v_res_1557_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1556_, v_s_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1558_, lean_object* v_pattern_1559_, lean_object* v_replacement_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1558_, v_replacement_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1562_, lean_object* v_pattern_1563_, lean_object* v_replacement_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1562_, v_pattern_1563_, v_replacement_1564_);
lean_dec_ref(v_replacement_1564_);
lean_dec_ref(v_pattern_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1566_, lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v_inst_1569_, lean_object* v_R_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1566_, v___x_1567_, v___x_1568_, v_a_1571_, v_b_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1574_, lean_object* v___x_1575_, lean_object* v___x_1576_, lean_object* v_inst_1577_, lean_object* v_R_1578_, lean_object* v_a_1579_, lean_object* v_b_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1574_, v___x_1575_, v___x_1576_, v_inst_1577_, v_R_1578_, v_a_1579_, v_b_1580_);
lean_dec_ref(v___x_1575_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_as_1583_, lean_object* v_lo_1584_, lean_object* v_hi_1585_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_nat_dec_lt(v_lo_1584_, v_hi_1585_);
if (v___x_1586_ == 0)
{
lean_dec(v_lo_1584_);
return v_as_1583_;
}
else
{
lean_object* v___f_1587_; lean_object* v___x_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; uint8_t v___x_1591_; 
v___f_1587_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___closed__0));
lean_inc(v_lo_1584_);
v___x_1588_ = l_Array_qpartition___redArg(v_as_1583_, v___f_1587_, v_lo_1584_, v_hi_1585_);
v_fst_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_fst_1589_);
v_snd_1590_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_snd_1590_);
lean_dec_ref(v___x_1588_);
v___x_1591_ = lean_nat_dec_le(v_hi_1585_, v_fst_1589_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_snd_1590_, v_lo_1584_, v_fst_1589_);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v_fst_1589_, v___x_1593_);
lean_dec(v_fst_1589_);
v_as_1583_ = v___x_1592_;
v_lo_1584_ = v___x_1594_;
goto _start;
}
else
{
lean_dec(v_fst_1589_);
lean_dec(v_lo_1584_);
return v_snd_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_as_1596_, lean_object* v_lo_1597_, lean_object* v_hi_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_as_1596_, v_lo_1597_, v_hi_1598_);
lean_dec(v_hi_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1600_, lean_object* v_msgs_1601_){
_start:
{
if (v_mode_1600_ == 0)
{
return v_msgs_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1602_ = lean_array_mk(v_msgs_1601_);
v___x_1608_ = lean_array_get_size(v___x_1602_);
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_nat_dec_eq(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___y_1614_; uint8_t v___x_1616_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_nat_sub(v___x_1608_, v___x_1611_);
v___x_1616_ = lean_nat_dec_le(v___x_1609_, v___x_1612_);
if (v___x_1616_ == 0)
{
lean_inc(v___x_1612_);
v___y_1614_ = v___x_1612_;
goto v___jp_1613_;
}
else
{
v___y_1614_ = v___x_1609_;
goto v___jp_1613_;
}
v___jp_1613_:
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_nat_dec_le(v___y_1614_, v___x_1612_);
if (v___x_1615_ == 0)
{
lean_dec(v___x_1612_);
lean_inc(v___y_1614_);
v___y_1604_ = v___y_1614_;
v___y_1605_ = v___y_1614_;
goto v___jp_1603_;
}
else
{
v___y_1604_ = v___y_1614_;
v___y_1605_ = v___x_1612_;
goto v___jp_1603_;
}
}
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_array_to_list(v___x_1602_);
return v___x_1617_;
}
v___jp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1602_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
v___x_1607_ = lean_array_to_list(v___x_1606_);
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1618_, lean_object* v_msgs_1619_){
_start:
{
uint8_t v_mode_boxed_1620_; lean_object* v_res_1621_; 
v_mode_boxed_1620_ = lean_unbox(v_mode_1618_);
v_res_1621_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1620_, v_msgs_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1622_, lean_object* v_as_1623_, lean_object* v_lo_1624_, lean_object* v_hi_1625_, lean_object* v_w_1626_, lean_object* v_hlo_1627_, lean_object* v_hhi_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_as_1623_, v_lo_1624_, v_hi_1625_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1630_, lean_object* v_as_1631_, lean_object* v_lo_1632_, lean_object* v_hi_1633_, lean_object* v_w_1634_, lean_object* v_hlo_1635_, lean_object* v_hhi_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1630_, v_as_1631_, v_lo_1632_, v_hi_1633_, v_w_1634_, v_hlo_1635_, v_hhi_1636_);
lean_dec(v_hi_1633_);
lean_dec(v_n_1630_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1638_, size_t v_i_1639_, size_t v_stop_1640_, lean_object* v_b_1641_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_usize_dec_eq(v_i_1639_, v_stop_1640_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v_diagnostics_1644_; lean_object* v_msgLog_1645_; lean_object* v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; 
v___x_1643_ = lean_array_uget_borrowed(v_as_1638_, v_i_1639_);
v_diagnostics_1644_ = lean_ctor_get(v___x_1643_, 1);
v_msgLog_1645_ = lean_ctor_get(v_diagnostics_1644_, 0);
lean_inc_ref(v_msgLog_1645_);
v___x_1646_ = l_Lean_MessageLog_append(v_b_1641_, v_msgLog_1645_);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1639_, v___x_1647_);
v_i_1639_ = v___x_1648_;
v_b_1641_ = v___x_1646_;
goto _start;
}
else
{
return v_b_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1650_, lean_object* v_i_1651_, lean_object* v_stop_1652_, lean_object* v_b_1653_){
_start:
{
size_t v_i_boxed_1654_; size_t v_stop_boxed_1655_; lean_object* v_res_1656_; 
v_i_boxed_1654_ = lean_unbox_usize(v_i_1651_);
lean_dec(v_i_1651_);
v_stop_boxed_1655_ = lean_unbox_usize(v_stop_1652_);
lean_dec(v_stop_1652_);
v_res_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1650_, v_i_boxed_1654_, v_stop_boxed_1655_, v_b_1653_);
lean_dec_ref(v_as_1650_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1657_, size_t v_i_1658_, size_t v_stop_1659_, lean_object* v_b_1660_){
_start:
{
lean_object* v___y_1662_; uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_eq(v_i_1658_, v_stop_1659_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1667_ = lean_array_uget_borrowed(v_as_1657_, v_i_1658_);
v___x_1668_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1667_);
v___x_1669_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1667_);
v___x_1670_ = l_Lean_Language_SnapshotTree_getAll(v___x_1669_);
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_array_get_size(v___x_1670_);
v___x_1673_ = lean_nat_dec_lt(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref(v___x_1670_);
v___x_1674_ = l_Lean_MessageLog_append(v_b_1660_, v___x_1668_);
v___y_1662_ = v___x_1674_;
goto v___jp_1661_;
}
else
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_nat_dec_le(v___x_1672_, v___x_1672_);
if (v___x_1675_ == 0)
{
if (v___x_1673_ == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref(v___x_1670_);
v___x_1676_ = l_Lean_MessageLog_append(v_b_1660_, v___x_1668_);
v___y_1662_ = v___x_1676_;
goto v___jp_1661_;
}
else
{
size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = lean_usize_of_nat(v___x_1672_);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1670_, v___x_1677_, v___x_1678_, v___x_1668_);
lean_dec_ref(v___x_1670_);
v___x_1680_ = l_Lean_MessageLog_append(v_b_1660_, v___x_1679_);
v___y_1662_ = v___x_1680_;
goto v___jp_1661_;
}
}
else
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = lean_usize_of_nat(v___x_1672_);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1670_, v___x_1681_, v___x_1682_, v___x_1668_);
lean_dec_ref(v___x_1670_);
v___x_1684_ = l_Lean_MessageLog_append(v_b_1660_, v___x_1683_);
v___y_1662_ = v___x_1684_;
goto v___jp_1661_;
}
}
}
else
{
return v_b_1660_;
}
v___jp_1661_:
{
size_t v___x_1663_; size_t v___x_1664_; 
v___x_1663_ = ((size_t)1ULL);
v___x_1664_ = lean_usize_add(v_i_1658_, v___x_1663_);
v_i_1658_ = v___x_1664_;
v_b_1660_ = v___y_1662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1685_, lean_object* v_i_1686_, lean_object* v_stop_1687_, lean_object* v_b_1688_){
_start:
{
size_t v_i_boxed_1689_; size_t v_stop_boxed_1690_; lean_object* v_res_1691_; 
v_i_boxed_1689_ = lean_unbox_usize(v_i_1686_);
lean_dec(v_i_1686_);
v_stop_boxed_1690_ = lean_unbox_usize(v_stop_1687_);
lean_dec(v_stop_1687_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1685_, v_i_boxed_1689_, v_stop_boxed_1690_, v_b_1688_);
lean_dec_ref(v_as_1685_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_fileName_1698_; lean_object* v_fileMap_1699_; lean_object* v_currRecDepth_1700_; lean_object* v_cmdPos_1701_; lean_object* v_macroStack_1702_; lean_object* v_quotContext_x3f_1703_; lean_object* v_currMacroScope_1704_; lean_object* v_ref_1705_; lean_object* v_cancelTk_x3f_1706_; uint8_t v_suppressElabErrors_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_fileName_1698_ = lean_ctor_get(v_a_1695_, 0);
v_fileMap_1699_ = lean_ctor_get(v_a_1695_, 1);
v_currRecDepth_1700_ = lean_ctor_get(v_a_1695_, 2);
v_cmdPos_1701_ = lean_ctor_get(v_a_1695_, 3);
v_macroStack_1702_ = lean_ctor_get(v_a_1695_, 4);
v_quotContext_x3f_1703_ = lean_ctor_get(v_a_1695_, 5);
v_currMacroScope_1704_ = lean_ctor_get(v_a_1695_, 6);
v_ref_1705_ = lean_ctor_get(v_a_1695_, 7);
v_cancelTk_x3f_1706_ = lean_ctor_get(v_a_1695_, 9);
v_suppressElabErrors_1707_ = lean_ctor_get_uint8(v_a_1695_, sizeof(void*)*10);
v___x_1708_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1706_);
lean_inc(v_ref_1705_);
lean_inc(v_currMacroScope_1704_);
lean_inc(v_quotContext_x3f_1703_);
lean_inc(v_macroStack_1702_);
lean_inc(v_cmdPos_1701_);
lean_inc(v_currRecDepth_1700_);
lean_inc_ref(v_fileMap_1699_);
lean_inc_ref(v_fileName_1698_);
v___x_1709_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1709_, 0, v_fileName_1698_);
lean_ctor_set(v___x_1709_, 1, v_fileMap_1699_);
lean_ctor_set(v___x_1709_, 2, v_currRecDepth_1700_);
lean_ctor_set(v___x_1709_, 3, v_cmdPos_1701_);
lean_ctor_set(v___x_1709_, 4, v_macroStack_1702_);
lean_ctor_set(v___x_1709_, 5, v_quotContext_x3f_1703_);
lean_ctor_set(v___x_1709_, 6, v_currMacroScope_1704_);
lean_ctor_set(v___x_1709_, 7, v_ref_1705_);
lean_ctor_set(v___x_1709_, 8, v___x_1708_);
lean_ctor_set(v___x_1709_, 9, v_cancelTk_x3f_1706_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*10, v_suppressElabErrors_1707_);
v___x_1710_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1694_, v___x_1709_, v_a_1696_);
lean_dec_ref(v___x_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1756_; 
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1710_, 0);
lean_dec(v_unused_1757_);
v___x_1712_ = v___x_1710_;
v_isShared_1713_ = v_isSharedCheck_1756_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v___x_1710_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1756_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v_messages_1716_; lean_object* v___y_1718_; lean_object* v_snapshotTasks_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1714_ = lean_st_ref_get(v_a_1696_);
v___x_1715_ = lean_st_ref_get(v_a_1696_);
v_messages_1716_ = lean_ctor_get(v___x_1714_, 1);
lean_inc_ref(v_messages_1716_);
lean_dec(v___x_1714_);
v_snapshotTasks_1744_ = lean_ctor_get(v___x_1715_, 10);
lean_inc_ref(v_snapshotTasks_1744_);
lean_dec(v___x_1715_);
v___x_1745_ = l_Lean_MessageLog_empty;
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_array_get_size(v_snapshotTasks_1744_);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v_snapshotTasks_1744_);
v___y_1718_ = v___x_1745_;
goto v___jp_1717_;
}
else
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_nat_dec_le(v___x_1747_, v___x_1747_);
if (v___x_1749_ == 0)
{
if (v___x_1748_ == 0)
{
lean_dec_ref(v_snapshotTasks_1744_);
v___y_1718_ = v___x_1745_;
goto v___jp_1717_;
}
else
{
size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = lean_usize_of_nat(v___x_1747_);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1744_, v___x_1750_, v___x_1751_, v___x_1745_);
lean_dec_ref(v_snapshotTasks_1744_);
v___y_1718_ = v___x_1752_;
goto v___jp_1717_;
}
}
else
{
size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = lean_usize_of_nat(v___x_1747_);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1744_, v___x_1753_, v___x_1754_, v___x_1745_);
lean_dec_ref(v_snapshotTasks_1744_);
v___y_1718_ = v___x_1755_;
goto v___jp_1717_;
}
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v_env_1720_; lean_object* v_messages_1721_; lean_object* v_scopes_1722_; lean_object* v_usedQuotCtxts_1723_; lean_object* v_nextMacroScope_1724_; lean_object* v_maxRecDepth_1725_; lean_object* v_ngen_1726_; lean_object* v_auxDeclNGen_1727_; lean_object* v_infoState_1728_; lean_object* v_traceState_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1742_; 
v___x_1719_ = lean_st_ref_take(v_a_1696_);
v_env_1720_ = lean_ctor_get(v___x_1719_, 0);
v_messages_1721_ = lean_ctor_get(v___x_1719_, 1);
v_scopes_1722_ = lean_ctor_get(v___x_1719_, 2);
v_usedQuotCtxts_1723_ = lean_ctor_get(v___x_1719_, 3);
v_nextMacroScope_1724_ = lean_ctor_get(v___x_1719_, 4);
v_maxRecDepth_1725_ = lean_ctor_get(v___x_1719_, 5);
v_ngen_1726_ = lean_ctor_get(v___x_1719_, 6);
v_auxDeclNGen_1727_ = lean_ctor_get(v___x_1719_, 7);
v_infoState_1728_ = lean_ctor_get(v___x_1719_, 8);
v_traceState_1729_ = lean_ctor_get(v___x_1719_, 9);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1719_, 10);
lean_dec(v_unused_1743_);
v___x_1731_ = v___x_1719_;
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_traceState_1729_);
lean_inc(v_infoState_1728_);
lean_inc(v_auxDeclNGen_1727_);
lean_inc(v_ngen_1726_);
lean_inc(v_maxRecDepth_1725_);
lean_inc(v_nextMacroScope_1724_);
lean_inc(v_usedQuotCtxts_1723_);
lean_inc(v_scopes_1722_);
lean_inc(v_messages_1721_);
lean_inc(v_env_1720_);
lean_dec(v___x_1719_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 10, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_env_1720_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_messages_1721_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_scopes_1722_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_usedQuotCtxts_1723_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v_nextMacroScope_1724_);
lean_ctor_set(v_reuseFailAlloc_1741_, 5, v_maxRecDepth_1725_);
lean_ctor_set(v_reuseFailAlloc_1741_, 6, v_ngen_1726_);
lean_ctor_set(v_reuseFailAlloc_1741_, 7, v_auxDeclNGen_1727_);
lean_ctor_set(v_reuseFailAlloc_1741_, 8, v_infoState_1728_);
lean_ctor_set(v_reuseFailAlloc_1741_, 9, v_traceState_1729_);
lean_ctor_set(v_reuseFailAlloc_1741_, 10, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = lean_st_ref_set(v_a_1696_, v___x_1735_);
v___x_1737_ = l_Lean_MessageLog_append(v_messages_1716_, v___y_1718_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1737_);
v___x_1739_ = v___x_1712_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1710_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1710_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1766_, v_a_1767_, v_a_1768_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1771_, lean_object* v_opt_1772_){
_start:
{
lean_object* v_name_1773_; lean_object* v_defValue_1774_; lean_object* v_map_1775_; lean_object* v___x_1776_; 
v_name_1773_ = lean_ctor_get(v_opt_1772_, 0);
v_defValue_1774_ = lean_ctor_get(v_opt_1772_, 1);
v_map_1775_ = lean_ctor_get(v_opts_1771_, 0);
v___x_1776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1775_, v_name_1773_);
if (lean_obj_tag(v___x_1776_) == 0)
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_unbox(v_defValue_1774_);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; 
v_val_1778_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1778_);
lean_dec_ref(v___x_1776_);
if (lean_obj_tag(v_val_1778_) == 1)
{
uint8_t v_v_1779_; 
v_v_1779_ = lean_ctor_get_uint8(v_val_1778_, 0);
lean_dec_ref(v_val_1778_);
return v_v_1779_;
}
else
{
uint8_t v___x_1780_; 
lean_dec(v_val_1778_);
v___x_1780_ = lean_unbox(v_defValue_1774_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1781_, lean_object* v_opt_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1781_, v_opt_1782_);
lean_dec_ref(v_opt_1782_);
lean_dec_ref(v_opts_1781_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1789_);
lean_dec_ref(v_s_1789_);
return v_res_1790_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_box(1);
v___x_1792_ = l_Lean_MessageData_ofFormat(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1797_ = l_Lean_MessageData_ofFormat(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
if (lean_obj_tag(v_x_1799_) == 0)
{
return v_x_1798_;
}
else
{
lean_object* v_head_1800_; lean_object* v_tail_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1823_; 
v_head_1800_ = lean_ctor_get(v_x_1799_, 0);
v_tail_1801_ = lean_ctor_get(v_x_1799_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1799_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1803_ = v_x_1799_;
v_isShared_1804_ = v_isSharedCheck_1823_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_tail_1801_);
lean_inc(v_head_1800_);
lean_dec(v_x_1799_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1823_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_before_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1821_; 
v_before_1805_ = lean_ctor_get(v_head_1800_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_head_1800_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v_head_1800_, 1);
lean_dec(v_unused_1822_);
v___x_1807_ = v_head_1800_;
v_isShared_1808_ = v_isSharedCheck_1821_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_before_1805_);
lean_dec(v_head_1800_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1821_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 7);
lean_ctor_set(v___x_1807_, 1, v___x_1809_);
lean_ctor_set(v___x_1807_, 0, v_x_1798_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_x_1798_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 7);
lean_ctor_set(v___x_1803_, 1, v___x_1812_);
lean_ctor_set(v___x_1803_, 0, v___x_1811_);
v___x_1814_ = v___x_1803_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = l_Lean_MessageData_ofSyntax(v_before_1805_);
v___x_1816_ = l_Lean_indentD(v___x_1815_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1814_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v_x_1798_ = v___x_1817_;
v_x_1799_ = v_tail_1801_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1828_ = l_Lean_MessageData_ofFormat(v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1829_, lean_object* v_macroStack_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; lean_object* v_scopes_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_opts_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1833_ = lean_st_ref_get(v___y_1831_);
v_scopes_1834_ = lean_ctor_get(v___x_1833_, 2);
lean_inc(v_scopes_1834_);
lean_dec(v___x_1833_);
v___x_1835_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1836_ = l_List_head_x21___redArg(v___x_1835_, v_scopes_1834_);
lean_dec(v_scopes_1834_);
v_opts_1837_ = lean_ctor_get(v___x_1836_, 1);
lean_inc_ref(v_opts_1837_);
lean_dec(v___x_1836_);
v___x_1838_ = l_Lean_Elab_pp_macroStack;
v___x_1839_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1837_, v___x_1838_);
lean_dec_ref(v_opts_1837_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
lean_dec(v_macroStack_1830_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_msgData_1829_);
return v___x_1840_;
}
else
{
if (lean_obj_tag(v_macroStack_1830_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_msgData_1829_);
return v___x_1841_;
}
else
{
lean_object* v_head_1842_; lean_object* v_after_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1858_; 
v_head_1842_ = lean_ctor_get(v_macroStack_1830_, 0);
lean_inc(v_head_1842_);
v_after_1843_ = lean_ctor_get(v_head_1842_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_head_1842_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_head_1842_, 0);
lean_dec(v_unused_1859_);
v___x_1845_ = v_head_1842_;
v_isShared_1846_ = v_isSharedCheck_1858_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_after_1843_);
lean_dec(v_head_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1858_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 7);
lean_ctor_set(v___x_1845_, 1, v___x_1847_);
lean_ctor_set(v___x_1845_, 0, v_msgData_1829_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_msgData_1829_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_msgData_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1850_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_MessageData_ofSyntax(v_after_1843_);
v___x_1853_ = l_Lean_indentD(v___x_1852_);
v_msgData_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1854_, 0, v___x_1851_);
lean_ctor_set(v_msgData_1854_, 1, v___x_1853_);
v___x_1855_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1854_, v_macroStack_1830_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1860_, lean_object* v_macroStack_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1860_, v_macroStack_1861_, v___y_1862_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
lean_ctor_set(v___x_1870_, 2, v___x_1869_);
lean_ctor_set(v___x_1870_, 3, v___x_1868_);
lean_ctor_set(v___x_1870_, 4, v___x_1868_);
lean_ctor_set(v___x_1870_, 5, v___x_1868_);
lean_ctor_set(v___x_1870_, 6, v___x_1868_);
lean_ctor_set(v___x_1870_, 7, v___x_1868_);
lean_ctor_set(v___x_1870_, 8, v___x_1868_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_unsigned_to_nat(32u);
v___x_1872_ = lean_mk_empty_array_with_capacity(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = ((size_t)5ULL);
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_unsigned_to_nat(32u);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___x_1876_);
v___x_1878_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1879_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1877_);
lean_ctor_set(v___x_1879_, 2, v___x_1875_);
lean_ctor_set(v___x_1879_, 3, v___x_1875_);
lean_ctor_set_usize(v___x_1879_, 4, v___x_1874_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1880_ = lean_box(1);
v___x_1881_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1882_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1881_);
lean_ctor_set(v___x_1883_, 2, v___x_1880_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_env_1888_; lean_object* v___x_1889_; lean_object* v_scopes_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_opts_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1887_ = lean_st_ref_get(v___y_1885_);
v_env_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_env_1888_);
lean_dec(v___x_1887_);
v___x_1889_ = lean_st_ref_get(v___y_1885_);
v_scopes_1890_ = lean_ctor_get(v___x_1889_, 2);
lean_inc(v_scopes_1890_);
lean_dec(v___x_1889_);
v___x_1891_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1892_ = l_List_head_x21___redArg(v___x_1891_, v_scopes_1890_);
lean_dec(v_scopes_1890_);
v_opts_1893_ = lean_ctor_get(v___x_1892_, 1);
lean_inc_ref(v_opts_1893_);
lean_dec(v___x_1892_);
v___x_1894_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1895_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1896_, 0, v_env_1888_);
lean_ctor_set(v___x_1896_, 1, v___x_1894_);
lean_ctor_set(v___x_1896_, 2, v___x_1895_);
lean_ctor_set(v___x_1896_, 3, v_opts_1893_);
v___x_1897_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v_msgData_1884_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1899_, v___y_1900_);
lean_dec(v___y_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Elab_Command_getRef___redArg(v___y_1904_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v_macroStack_1909_; lean_object* v___x_1910_; lean_object* v_a_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1922_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1907_);
v_macroStack_1909_ = lean_ctor_get(v___y_1904_, 4);
lean_inc(v_macroStack_1909_);
lean_dec_ref(v___y_1904_);
v___x_1910_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1903_, v___y_1905_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
lean_inc(v_macroStack_1909_);
v___x_1912_ = l_Lean_Elab_getBetterRef(v_a_1908_, v_macroStack_1909_);
lean_dec(v_a_1908_);
v___x_1913_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1911_, v_macroStack_1909_, v___y_1905_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1912_);
lean_ctor_set(v___x_1918_, 1, v_a_1914_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 0, v___x_1918_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_msg_1903_);
v_a_1923_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1907_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1907_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_Elab_Command_getRef___redArg(v___y_1938_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_fileName_1943_; lean_object* v_fileMap_1944_; lean_object* v_currRecDepth_1945_; lean_object* v_cmdPos_1946_; lean_object* v_macroStack_1947_; lean_object* v_quotContext_x3f_1948_; lean_object* v_currMacroScope_1949_; lean_object* v_snap_x3f_1950_; lean_object* v_cancelTk_x3f_1951_; uint8_t v_suppressElabErrors_1952_; lean_object* v_ref_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v_fileName_1943_ = lean_ctor_get(v___y_1938_, 0);
v_fileMap_1944_ = lean_ctor_get(v___y_1938_, 1);
v_currRecDepth_1945_ = lean_ctor_get(v___y_1938_, 2);
v_cmdPos_1946_ = lean_ctor_get(v___y_1938_, 3);
v_macroStack_1947_ = lean_ctor_get(v___y_1938_, 4);
v_quotContext_x3f_1948_ = lean_ctor_get(v___y_1938_, 5);
v_currMacroScope_1949_ = lean_ctor_get(v___y_1938_, 6);
v_snap_x3f_1950_ = lean_ctor_get(v___y_1938_, 8);
v_cancelTk_x3f_1951_ = lean_ctor_get(v___y_1938_, 9);
v_suppressElabErrors_1952_ = lean_ctor_get_uint8(v___y_1938_, sizeof(void*)*10);
v_ref_1953_ = l_Lean_replaceRef(v_ref_1936_, v_a_1942_);
lean_dec(v_a_1942_);
lean_inc(v_cancelTk_x3f_1951_);
lean_inc(v_snap_x3f_1950_);
lean_inc(v_currMacroScope_1949_);
lean_inc(v_quotContext_x3f_1948_);
lean_inc(v_macroStack_1947_);
lean_inc(v_cmdPos_1946_);
lean_inc(v_currRecDepth_1945_);
lean_inc_ref(v_fileMap_1944_);
lean_inc_ref(v_fileName_1943_);
v___x_1954_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1954_, 0, v_fileName_1943_);
lean_ctor_set(v___x_1954_, 1, v_fileMap_1944_);
lean_ctor_set(v___x_1954_, 2, v_currRecDepth_1945_);
lean_ctor_set(v___x_1954_, 3, v_cmdPos_1946_);
lean_ctor_set(v___x_1954_, 4, v_macroStack_1947_);
lean_ctor_set(v___x_1954_, 5, v_quotContext_x3f_1948_);
lean_ctor_set(v___x_1954_, 6, v_currMacroScope_1949_);
lean_ctor_set(v___x_1954_, 7, v_ref_1953_);
lean_ctor_set(v___x_1954_, 8, v_snap_x3f_1950_);
lean_ctor_set(v___x_1954_, 9, v_cancelTk_x3f_1951_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*10, v_suppressElabErrors_1952_);
v___x_1955_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1937_, v___x_1954_, v___y_1939_);
return v___x_1955_;
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_msg_1937_);
v_a_1956_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1941_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1941_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_1964_, v_msg_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_ref_1964_);
return v_res_1969_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_1972_ = l_Lean_stringToMessageData(v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_val_1987_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = l_Lean_Syntax_getArg(v_stx_1976_, v___x_1994_);
switch(lean_obj_tag(v___x_1995_))
{
case 2:
{
lean_object* v_val_1996_; 
lean_dec(v_stx_1976_);
v_val_1996_ = lean_ctor_get(v___x_1995_, 1);
lean_inc_ref(v_val_1996_);
lean_dec_ref(v___x_1995_);
v_val_1987_ = v_val_1996_;
goto v___jp_1986_;
}
case 1:
{
lean_object* v_kind_1997_; 
v_kind_1997_ = lean_ctor_get(v___x_1995_, 1);
lean_inc(v_kind_1997_);
if (lean_obj_tag(v_kind_1997_) == 1)
{
lean_object* v_pre_1998_; 
v_pre_1998_ = lean_ctor_get(v_kind_1997_, 0);
lean_inc(v_pre_1998_);
if (lean_obj_tag(v_pre_1998_) == 1)
{
lean_object* v_pre_1999_; 
v_pre_1999_ = lean_ctor_get(v_pre_1998_, 0);
lean_inc(v_pre_1999_);
if (lean_obj_tag(v_pre_1999_) == 1)
{
lean_object* v_pre_2000_; 
v_pre_2000_ = lean_ctor_get(v_pre_1999_, 0);
lean_inc(v_pre_2000_);
if (lean_obj_tag(v_pre_2000_) == 1)
{
lean_object* v_pre_2001_; 
v_pre_2001_ = lean_ctor_get(v_pre_2000_, 0);
if (lean_obj_tag(v_pre_2001_) == 0)
{
lean_object* v_str_2002_; lean_object* v_str_2003_; lean_object* v_str_2004_; lean_object* v_str_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_str_2002_ = lean_ctor_get(v_kind_1997_, 1);
lean_inc_ref(v_str_2002_);
lean_dec_ref(v_kind_1997_);
v_str_2003_ = lean_ctor_get(v_pre_1998_, 1);
lean_inc_ref(v_str_2003_);
lean_dec_ref(v_pre_1998_);
v_str_2004_ = lean_ctor_get(v_pre_1999_, 1);
lean_inc_ref(v_str_2004_);
lean_dec_ref(v_pre_1999_);
v_str_2005_ = lean_ctor_get(v_pre_2000_, 1);
lean_inc_ref(v_str_2005_);
lean_dec_ref(v_pre_2000_);
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0));
v___x_2007_ = lean_string_dec_eq(v_str_2005_, v___x_2006_);
lean_dec_ref(v_str_2005_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v_str_2004_);
lean_dec_ref(v_str_2003_);
lean_dec_ref(v_str_2002_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
else
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2009_ = lean_string_dec_eq(v_str_2004_, v___x_2008_);
lean_dec_ref(v_str_2004_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v_str_2003_);
lean_dec_ref(v_str_2002_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2011_ = lean_string_dec_eq(v_str_2003_, v___x_2010_);
lean_dec_ref(v_str_2003_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v_str_2002_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
else
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2013_ = lean_string_dec_eq(v_str_2002_, v___x_2012_);
lean_dec_ref(v_str_2002_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = l_Lean_Syntax_getArg(v___x_1995_, v___x_2014_);
lean_dec_ref(v___x_1995_);
if (lean_obj_tag(v___x_2015_) == 2)
{
lean_object* v_val_2016_; 
lean_dec(v_stx_1976_);
v_val_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc_ref(v_val_2016_);
lean_dec_ref(v___x_2015_);
v_val_1987_ = v_val_2016_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v___x_2015_);
v___x_2017_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1976_);
v___x_2018_ = l_Lean_MessageData_ofSyntax(v_stx_1976_);
v___x_2019_ = l_Lean_indentD(v___x_2018_);
v___x_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2017_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1976_, v___x_2020_, v___y_1977_, v___y_1978_);
lean_dec(v_stx_1976_);
return v___x_2021_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2000_);
lean_dec_ref(v_pre_1999_);
lean_dec_ref(v_pre_1998_);
lean_dec_ref(v_kind_1997_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
}
else
{
lean_dec(v_pre_2000_);
lean_dec_ref(v_pre_1999_);
lean_dec_ref(v_pre_1998_);
lean_dec_ref(v_kind_1997_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
}
else
{
lean_dec(v_pre_1999_);
lean_dec_ref(v_pre_1998_);
lean_dec_ref(v_kind_1997_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
}
else
{
lean_dec(v_pre_1998_);
lean_dec_ref(v_kind_1997_);
lean_dec_ref(v___x_1995_);
goto v___jp_1980_;
}
}
else
{
lean_dec_ref(v___x_1995_);
lean_dec(v_kind_1997_);
goto v___jp_1980_;
}
}
default: 
{
lean_dec(v___x_1995_);
goto v___jp_1980_;
}
}
v___jp_1980_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1981_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1976_);
v___x_1982_ = l_Lean_MessageData_ofSyntax(v_stx_1976_);
v___x_1983_ = l_Lean_indentD(v___x_1982_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1981_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1976_, v___x_1984_, v___y_1977_, v___y_1978_);
lean_dec(v_stx_1976_);
return v___x_1985_;
}
v___jp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_string_utf8_byte_size(v_val_1987_);
v___x_1990_ = lean_unsigned_to_nat(2u);
v___x_1991_ = lean_nat_sub(v___x_1989_, v___x_1990_);
v___x_1992_ = lean_string_utf8_extract(v_val_1987_, v___x_1988_, v___x_1991_);
lean_dec(v___x_1991_);
lean_dec_ref(v_val_1987_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2027_, size_t v_sz_2028_, size_t v_i_2029_, lean_object* v_b_2030_){
_start:
{
lean_object* v_a_2032_; uint8_t v___x_2036_; 
v___x_2036_ = lean_usize_dec_lt(v_i_2029_, v_sz_2028_);
if (v___x_2036_ == 0)
{
return v_b_2030_;
}
else
{
lean_object* v_a_2037_; lean_object* v_fst_2038_; lean_object* v_snd_2039_; lean_object* v_out_2040_; uint8_t v___x_2041_; 
v_a_2037_ = lean_array_uget_borrowed(v_as_2027_, v_i_2029_);
v_fst_2038_ = lean_ctor_get(v_a_2037_, 0);
v_snd_2039_ = lean_ctor_get(v_a_2037_, 1);
v_out_2040_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2041_ = lean_string_dec_eq(v_snd_2039_, v_out_2040_);
if (v___x_2041_ == 0)
{
uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2042_ = lean_unbox(v_fst_2038_);
v___x_2043_ = l_Lean_Diff_Action_linePrefix(v___x_2042_);
v___x_2044_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2045_ = lean_string_append(v___x_2043_, v___x_2044_);
v___x_2046_ = lean_string_append(v___x_2045_, v_snd_2039_);
v___x_2047_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
v___x_2049_ = lean_string_append(v_b_2030_, v___x_2048_);
lean_dec_ref(v___x_2048_);
v_a_2032_ = v___x_2049_;
goto v___jp_2031_;
}
else
{
uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2050_ = lean_unbox(v_fst_2038_);
v___x_2051_ = l_Lean_Diff_Action_linePrefix(v___x_2050_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2053_ = lean_string_append(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_string_append(v_b_2030_, v___x_2053_);
lean_dec_ref(v___x_2053_);
v_a_2032_ = v___x_2054_;
goto v___jp_2031_;
}
}
v___jp_2031_:
{
size_t v___x_2033_; size_t v___x_2034_; 
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2029_, v___x_2033_);
v_i_2029_ = v___x_2034_;
v_b_2030_ = v_a_2032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2055_, lean_object* v_sz_2056_, lean_object* v_i_2057_, lean_object* v_b_2058_){
_start:
{
size_t v_sz_boxed_2059_; size_t v_i_boxed_2060_; lean_object* v_res_2061_; 
v_sz_boxed_2059_ = lean_unbox_usize(v_sz_2056_);
lean_dec(v_sz_2056_);
v_i_boxed_2060_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2055_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2058_);
lean_dec_ref(v_as_2055_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2062_){
_start:
{
lean_object* v_out_2063_; size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v_out_2063_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2064_ = lean_array_size(v_lines_2062_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2062_, v_sz_2064_, v___x_2065_, v_out_2063_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2067_);
lean_dec_ref(v_lines_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2069_, lean_object* v_as_x27_2070_, lean_object* v_b_2071_){
_start:
{
if (lean_obj_tag(v_as_x27_2070_) == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v_filterFn_2069_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_b_2071_);
return v___x_2073_;
}
else
{
lean_object* v_head_2074_; uint8_t v_isSilent_2075_; 
v_head_2074_ = lean_ctor_get(v_as_x27_2070_, 0);
v_isSilent_2075_ = lean_ctor_get_uint8(v_head_2074_, sizeof(void*)*5 + 2);
if (v_isSilent_2075_ == 0)
{
lean_object* v_tail_2076_; lean_object* v_fst_2077_; lean_object* v_snd_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2098_; 
lean_inc(v_head_2074_);
v_tail_2076_ = lean_ctor_get(v_as_x27_2070_, 1);
lean_inc(v_tail_2076_);
lean_dec_ref(v_as_x27_2070_);
v_fst_2077_ = lean_ctor_get(v_b_2071_, 0);
v_snd_2078_ = lean_ctor_get(v_b_2071_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_b_2071_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2080_ = v_b_2071_;
v_isShared_2081_ = v_isSharedCheck_2098_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_snd_2078_);
lean_inc(v_fst_2077_);
lean_dec(v_b_2071_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2098_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_inc_ref(v_filterFn_2069_);
lean_inc(v_head_2074_);
v___x_2082_ = lean_apply_1(v_filterFn_2069_, v_head_2074_);
v___x_2083_ = lean_unbox(v___x_2082_);
switch(v___x_2083_)
{
case 0:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = l_Lean_MessageLog_add(v_head_2074_, v_fst_2077_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2084_);
v___x_2086_ = v___x_2080_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_snd_2078_);
v___x_2086_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v_as_x27_2070_ = v_tail_2076_;
v_b_2071_ = v___x_2086_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2090_; 
lean_dec(v_head_2074_);
if (v_isShared_2081_ == 0)
{
v___x_2090_ = v___x_2080_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_fst_2077_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_snd_2078_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_as_x27_2070_ = v_tail_2076_;
v_b_2071_ = v___x_2090_;
goto _start;
}
}
default: 
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = l_Lean_MessageLog_add(v_head_2074_, v_snd_2078_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v___x_2093_);
v___x_2095_ = v___x_2080_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_fst_2077_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
v_as_x27_2070_ = v_tail_2076_;
v_b_2071_ = v___x_2095_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2099_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2109_; 
v_tail_2099_ = lean_ctor_get(v_as_x27_2070_, 1);
lean_inc(v_tail_2099_);
lean_dec_ref(v_as_x27_2070_);
v_fst_2100_ = lean_ctor_get(v_b_2071_, 0);
v_snd_2101_ = lean_ctor_get(v_b_2071_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_b_2071_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2103_ = v_b_2071_;
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_snd_2101_);
lean_inc(v_fst_2100_);
lean_dec(v_b_2071_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fst_2100_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_snd_2101_);
v___x_2106_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
v_as_x27_2070_ = v_tail_2099_;
v_b_2071_ = v___x_2106_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2110_, lean_object* v_as_x27_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2110_, v_as_x27_2111_, v_b_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2115_, lean_object* v_a_2116_, uint8_t v_b_2117_){
_start:
{
uint8_t v___x_2118_; 
v___x_2118_ = 0;
switch(lean_obj_tag(v_a_2116_))
{
case 0:
{
uint8_t v___x_2119_; 
lean_dec_ref(v_a_2116_);
v___x_2119_ = 1;
return v___x_2119_;
}
case 1:
{
lean_object* v_pos_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2133_; 
v_pos_2120_ = lean_ctor_get(v_a_2116_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2122_ = v_a_2116_;
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_pos_2120_);
lean_dec(v_a_2116_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_str_2124_; lean_object* v_startInclusive_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v_str_2124_ = lean_ctor_get(v_s_2115_, 0);
v_startInclusive_2125_ = lean_ctor_get(v_s_2115_, 1);
v___x_2126_ = lean_nat_add(v_startInclusive_2125_, v_pos_2120_);
lean_dec(v_pos_2120_);
v___x_2127_ = lean_string_utf8_next_fast(v_str_2124_, v___x_2126_);
lean_dec(v___x_2126_);
v___x_2128_ = lean_nat_sub(v___x_2127_, v_startInclusive_2125_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2128_);
v___x_2130_ = v___x_2122_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v_a_2116_ = v___x_2130_;
v_b_2117_ = v___x_2118_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2134_; lean_object* v_table_2135_; lean_object* v_stackPos_2136_; lean_object* v_needlePos_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2190_; 
v_needle_2134_ = lean_ctor_get(v_a_2116_, 0);
v_table_2135_ = lean_ctor_get(v_a_2116_, 1);
v_stackPos_2136_ = lean_ctor_get(v_a_2116_, 2);
v_needlePos_2137_ = lean_ctor_get(v_a_2116_, 3);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2139_ = v_a_2116_;
v_isShared_2140_ = v_isSharedCheck_2190_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_needlePos_2137_);
lean_inc(v_stackPos_2136_);
lean_inc(v_table_2135_);
lean_inc(v_needle_2134_);
lean_dec(v_a_2116_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2190_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_str_2141_; lean_object* v_startInclusive_2142_; lean_object* v_endExclusive_2143_; lean_object* v_str_2144_; lean_object* v_startInclusive_2145_; lean_object* v_endExclusive_2146_; lean_object* v_basePos_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_str_2141_ = lean_ctor_get(v_needle_2134_, 0);
v_startInclusive_2142_ = lean_ctor_get(v_needle_2134_, 1);
v_endExclusive_2143_ = lean_ctor_get(v_needle_2134_, 2);
v_str_2144_ = lean_ctor_get(v_s_2115_, 0);
v_startInclusive_2145_ = lean_ctor_get(v_s_2115_, 1);
v_endExclusive_2146_ = lean_ctor_get(v_s_2115_, 2);
v_basePos_2147_ = lean_nat_sub(v_stackPos_2136_, v_needlePos_2137_);
v___x_2148_ = lean_nat_sub(v_endExclusive_2143_, v_startInclusive_2142_);
v___x_2149_ = lean_nat_add(v_basePos_2147_, v___x_2148_);
v___x_2150_ = lean_nat_sub(v_endExclusive_2146_, v_startInclusive_2145_);
v___x_2151_ = lean_nat_dec_le(v___x_2149_, v___x_2150_);
lean_dec(v___x_2149_);
if (v___x_2151_ == 0)
{
uint8_t v___x_2152_; 
lean_dec(v___x_2148_);
lean_del_object(v___x_2139_);
lean_dec(v_needlePos_2137_);
lean_dec(v_stackPos_2136_);
lean_dec_ref(v_table_2135_);
lean_dec_ref(v_needle_2134_);
v___x_2152_ = l_String_instDecidableLtRaw___aux__1(v_basePos_2147_, v___x_2150_);
lean_dec(v___x_2150_);
lean_dec(v_basePos_2147_);
if (v___x_2152_ == 0)
{
return v_b_2117_;
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_box(3);
v_a_2116_ = v___x_2153_;
v_b_2117_ = v___x_2118_;
goto _start;
}
}
else
{
lean_object* v___x_2155_; uint8_t v_stackByte_2156_; lean_object* v___x_2157_; uint8_t v_patByte_2158_; uint8_t v___x_2159_; 
lean_dec(v___x_2150_);
lean_dec(v_basePos_2147_);
v___x_2155_ = lean_nat_add(v_startInclusive_2145_, v_stackPos_2136_);
v_stackByte_2156_ = lean_string_get_byte_fast(v_str_2144_, v___x_2155_);
v___x_2157_ = lean_nat_add(v_startInclusive_2142_, v_needlePos_2137_);
v_patByte_2158_ = lean_string_get_byte_fast(v_str_2141_, v___x_2157_);
v___x_2159_ = lean_uint8_dec_eq(v_stackByte_2156_, v_patByte_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
lean_dec(v___x_2148_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = lean_nat_dec_eq(v_needlePos_2137_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_newNeedlePos_2164_; uint8_t v___x_2165_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_nat_sub(v_needlePos_2137_, v___x_2162_);
lean_dec(v_needlePos_2137_);
v_newNeedlePos_2164_ = lean_array_fget_borrowed(v_table_2135_, v___x_2163_);
lean_dec(v___x_2163_);
v___x_2165_ = lean_nat_dec_eq(v_newNeedlePos_2164_, v___x_2160_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2167_; 
lean_inc(v_newNeedlePos_2164_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 3, v_newNeedlePos_2164_);
v___x_2167_ = v___x_2139_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_needle_2134_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_table_2135_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_stackPos_2136_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_newNeedlePos_2164_);
v___x_2167_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
v_a_2116_ = v___x_2167_;
v_b_2117_ = v___x_2118_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2170_; lean_object* v___x_2172_; 
v_nextStackPos_2170_ = l_String_Slice_posGE___redArg(v_s_2115_, v_stackPos_2136_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 3, v___x_2160_);
lean_ctor_set(v___x_2139_, 2, v_nextStackPos_2170_);
v___x_2172_ = v___x_2139_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_needle_2134_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_table_2135_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_nextStackPos_2170_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v___x_2160_);
v___x_2172_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_a_2116_ = v___x_2172_;
v_b_2117_ = v___x_2118_;
goto _start;
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_nextStackPos_2177_; lean_object* v___x_2179_; 
lean_dec(v_needlePos_2137_);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_add(v_stackPos_2136_, v___x_2175_);
lean_dec(v_stackPos_2136_);
v_nextStackPos_2177_ = l_String_Slice_posGE___redArg(v_s_2115_, v___x_2176_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 3, v___x_2160_);
lean_ctor_set(v___x_2139_, 2, v_nextStackPos_2177_);
v___x_2179_ = v___x_2139_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_needle_2134_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_table_2135_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_nextStackPos_2177_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v___x_2160_);
v___x_2179_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
v_a_2116_ = v___x_2179_;
v_b_2117_ = v___x_2118_;
goto _start;
}
}
}
else
{
lean_object* v___x_2182_; lean_object* v_nextNeedlePos_2183_; uint8_t v___x_2184_; 
v___x_2182_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2183_ = lean_nat_add(v_needlePos_2137_, v___x_2182_);
lean_dec(v_needlePos_2137_);
v___x_2184_ = lean_nat_dec_eq(v_nextNeedlePos_2183_, v___x_2148_);
lean_dec(v___x_2148_);
if (v___x_2184_ == 0)
{
lean_object* v_nextStackPos_2185_; lean_object* v___x_2187_; 
v_nextStackPos_2185_ = lean_nat_add(v_stackPos_2136_, v___x_2182_);
lean_dec(v_stackPos_2136_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 3, v_nextNeedlePos_2183_);
lean_ctor_set(v___x_2139_, 2, v_nextStackPos_2185_);
v___x_2187_ = v___x_2139_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_needle_2134_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_table_2135_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_nextStackPos_2185_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_nextNeedlePos_2183_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
v_a_2116_ = v___x_2187_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2183_);
lean_del_object(v___x_2139_);
lean_dec(v_stackPos_2136_);
lean_dec_ref(v_table_2135_);
lean_dec_ref(v_needle_2134_);
return v___x_2184_;
}
}
}
}
}
default: 
{
return v_b_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2191_, lean_object* v_a_2192_, lean_object* v_b_2193_){
_start:
{
uint8_t v_b_boxed_2194_; uint8_t v_res_2195_; lean_object* v_r_2196_; 
v_b_boxed_2194_ = lean_unbox(v_b_2193_);
v_res_2195_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2191_, v_a_2192_, v_b_boxed_2194_);
lean_dec_ref(v_s_2191_);
v_r_2196_ = lean_box(v_res_2195_);
return v_r_2196_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2197_, lean_object* v_s_2198_){
_start:
{
lean_object* v___y_2200_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = lean_string_utf8_byte_size(v___x_2197_);
v___x_2205_ = lean_nat_dec_eq(v___x_2204_, v___x_2203_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2197_);
lean_ctor_set(v___x_2206_, 1, v___x_2203_);
lean_ctor_set(v___x_2206_, 2, v___x_2204_);
v___x_2207_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2206_);
v___x_2208_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_ctor_set(v___x_2208_, 2, v___x_2203_);
lean_ctor_set(v___x_2208_, 3, v___x_2203_);
v___y_2200_ = v___x_2208_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2209_; 
lean_dec_ref(v___x_2197_);
v___x_2209_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2200_ = v___x_2209_;
goto v___jp_2199_;
}
v___jp_2199_:
{
uint8_t v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = 0;
v___x_2202_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2198_, v___y_2200_, v___x_2201_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2210_, lean_object* v_s_2211_){
_start:
{
uint8_t v_res_2212_; lean_object* v_r_2213_; 
v_res_2212_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2210_, v_s_2211_);
lean_dec_ref(v_s_2211_);
v_r_2213_ = lean_box(v_res_2212_);
return v_r_2213_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2214_, uint8_t v_suppressElabErrors_2215_, lean_object* v_x_2216_){
_start:
{
if (lean_obj_tag(v_x_2216_) == 1)
{
lean_object* v_pre_2217_; 
v_pre_2217_ = lean_ctor_get(v_x_2216_, 0);
if (lean_obj_tag(v_pre_2217_) == 0)
{
lean_object* v_str_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v_str_2218_ = lean_ctor_get(v_x_2216_, 1);
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2220_ = lean_string_dec_eq(v_str_2218_, v___x_2219_);
if (v___x_2220_ == 0)
{
return v___y_2214_;
}
else
{
return v_suppressElabErrors_2215_;
}
}
else
{
return v___y_2214_;
}
}
else
{
return v___y_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2221_, lean_object* v_suppressElabErrors_2222_, lean_object* v_x_2223_){
_start:
{
uint8_t v___y_29316__boxed_2224_; uint8_t v_suppressElabErrors_boxed_2225_; uint8_t v_res_2226_; lean_object* v_r_2227_; 
v___y_29316__boxed_2224_ = lean_unbox(v___y_2221_);
v_suppressElabErrors_boxed_2225_ = lean_unbox(v_suppressElabErrors_2222_);
v_res_2226_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29316__boxed_2224_, v_suppressElabErrors_boxed_2225_, v_x_2223_);
lean_dec(v_x_2223_);
v_r_2227_ = lean_box(v_res_2226_);
return v_r_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2228_, lean_object* v_msgData_2229_, uint8_t v_severity_2230_, uint8_t v_isSilent_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; uint8_t v___y_2241_; uint8_t v___y_2242_; lean_object* v___y_2243_; uint8_t v___y_2299_; lean_object* v___y_2300_; uint8_t v___y_2301_; uint8_t v___y_2302_; lean_object* v___y_2303_; uint8_t v___y_2327_; lean_object* v___y_2328_; uint8_t v___y_2329_; uint8_t v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2335_; uint8_t v___y_2336_; uint8_t v___y_2337_; uint8_t v___x_2352_; uint8_t v___y_2354_; uint8_t v___y_2355_; uint8_t v___y_2356_; uint8_t v___y_2358_; uint8_t v___x_2370_; 
v___x_2352_ = 2;
v___x_2370_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2230_, v___x_2352_);
if (v___x_2370_ == 0)
{
v___y_2358_ = v___x_2370_;
goto v___jp_2357_;
}
else
{
uint8_t v___x_2371_; 
lean_inc_ref(v_msgData_2229_);
v___x_2371_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2229_);
v___y_2358_ = v___x_2371_;
goto v___jp_2357_;
}
v___jp_2235_:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Elab_Command_getScope___redArg(v___y_2243_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = l_Lean_Elab_Command_getScope___redArg(v___y_2243_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2281_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2281_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2281_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v_currNamespace_2252_; lean_object* v_openDecls_2253_; lean_object* v_env_2254_; lean_object* v_messages_2255_; lean_object* v_scopes_2256_; lean_object* v_usedQuotCtxts_2257_; lean_object* v_nextMacroScope_2258_; lean_object* v_maxRecDepth_2259_; lean_object* v_ngen_2260_; lean_object* v_auxDeclNGen_2261_; lean_object* v_infoState_2262_; lean_object* v_traceState_2263_; lean_object* v_snapshotTasks_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2280_; 
v___x_2251_ = lean_st_ref_take(v___y_2243_);
v_currNamespace_2252_ = lean_ctor_get(v_a_2245_, 2);
lean_inc(v_currNamespace_2252_);
lean_dec(v_a_2245_);
v_openDecls_2253_ = lean_ctor_get(v_a_2247_, 3);
lean_inc(v_openDecls_2253_);
lean_dec(v_a_2247_);
v_env_2254_ = lean_ctor_get(v___x_2251_, 0);
v_messages_2255_ = lean_ctor_get(v___x_2251_, 1);
v_scopes_2256_ = lean_ctor_get(v___x_2251_, 2);
v_usedQuotCtxts_2257_ = lean_ctor_get(v___x_2251_, 3);
v_nextMacroScope_2258_ = lean_ctor_get(v___x_2251_, 4);
v_maxRecDepth_2259_ = lean_ctor_get(v___x_2251_, 5);
v_ngen_2260_ = lean_ctor_get(v___x_2251_, 6);
v_auxDeclNGen_2261_ = lean_ctor_get(v___x_2251_, 7);
v_infoState_2262_ = lean_ctor_get(v___x_2251_, 8);
v_traceState_2263_ = lean_ctor_get(v___x_2251_, 9);
v_snapshotTasks_2264_ = lean_ctor_get(v___x_2251_, 10);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2266_ = v___x_2251_;
v_isShared_2267_ = v_isSharedCheck_2280_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_snapshotTasks_2264_);
lean_inc(v_traceState_2263_);
lean_inc(v_infoState_2262_);
lean_inc(v_auxDeclNGen_2261_);
lean_inc(v_ngen_2260_);
lean_inc(v_maxRecDepth_2259_);
lean_inc(v_nextMacroScope_2258_);
lean_inc(v_usedQuotCtxts_2257_);
lean_inc(v_scopes_2256_);
lean_inc(v_messages_2255_);
lean_inc(v_env_2254_);
lean_dec(v___x_2251_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2280_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_currNamespace_2252_);
lean_ctor_set(v___x_2268_, 1, v_openDecls_2253_);
v___x_2269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___y_2239_);
v___x_2270_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2270_, 0, v___y_2240_);
lean_ctor_set(v___x_2270_, 1, v___y_2237_);
lean_ctor_set(v___x_2270_, 2, v___y_2236_);
lean_ctor_set(v___x_2270_, 3, v___y_2238_);
lean_ctor_set(v___x_2270_, 4, v___x_2269_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*5, v___y_2242_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*5 + 1, v___y_2241_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*5 + 2, v_isSilent_2231_);
v___x_2271_ = l_Lean_MessageLog_add(v___x_2270_, v_messages_2255_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 1, v___x_2271_);
v___x_2273_ = v___x_2266_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_env_2254_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_scopes_2256_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_usedQuotCtxts_2257_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_nextMacroScope_2258_);
lean_ctor_set(v_reuseFailAlloc_2279_, 5, v_maxRecDepth_2259_);
lean_ctor_set(v_reuseFailAlloc_2279_, 6, v_ngen_2260_);
lean_ctor_set(v_reuseFailAlloc_2279_, 7, v_auxDeclNGen_2261_);
lean_ctor_set(v_reuseFailAlloc_2279_, 8, v_infoState_2262_);
lean_ctor_set(v_reuseFailAlloc_2279_, 9, v_traceState_2263_);
lean_ctor_set(v_reuseFailAlloc_2279_, 10, v_snapshotTasks_2264_);
v___x_2273_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2274_ = lean_st_ref_set(v___y_2243_, v___x_2273_);
v___x_2275_ = lean_box(0);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2275_);
v___x_2277_ = v___x_2249_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2245_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
v_a_2282_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2246_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2246_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
v_a_2290_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2244_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2244_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
v___jp_2298_:
{
lean_object* v_fileName_2304_; lean_object* v_fileMap_2305_; uint8_t v_suppressElabErrors_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2325_; 
v_fileName_2304_ = lean_ctor_get(v___y_2232_, 0);
lean_inc_ref(v_fileName_2304_);
v_fileMap_2305_ = lean_ctor_get(v___y_2232_, 1);
lean_inc_ref(v_fileMap_2305_);
v_suppressElabErrors_2306_ = lean_ctor_get_uint8(v___y_2232_, sizeof(void*)*10);
lean_dec_ref(v___y_2232_);
v___x_2307_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2229_);
v___x_2308_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2307_, v___y_2233_);
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc_ref(v_fileMap_2305_);
v___x_2313_ = l_Lean_FileMap_toPosition(v_fileMap_2305_, v___y_2300_);
lean_dec(v___y_2300_);
v___x_2314_ = l_Lean_FileMap_toPosition(v_fileMap_2305_, v___y_2303_);
lean_dec(v___y_2303_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2306_ == 0)
{
lean_del_object(v___x_2311_);
v___y_2236_ = v___x_2315_;
v___y_2237_ = v___x_2313_;
v___y_2238_ = v___x_2316_;
v___y_2239_ = v_a_2309_;
v___y_2240_ = v_fileName_2304_;
v___y_2241_ = v___y_2301_;
v___y_2242_ = v___y_2302_;
v___y_2243_ = v___y_2233_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; uint8_t v___x_2320_; 
v___x_2317_ = lean_box(v___y_2299_);
v___x_2318_ = lean_box(v_suppressElabErrors_2306_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2319_, 0, v___x_2317_);
lean_closure_set(v___f_2319_, 1, v___x_2318_);
lean_inc(v_a_2309_);
v___x_2320_ = l_Lean_MessageData_hasTag(v___f_2319_, v_a_2309_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
lean_dec_ref(v___x_2315_);
lean_dec_ref(v___x_2313_);
lean_dec(v_a_2309_);
lean_dec_ref(v_fileName_2304_);
v___x_2321_ = lean_box(0);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2321_);
v___x_2323_ = v___x_2311_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
else
{
lean_del_object(v___x_2311_);
v___y_2236_ = v___x_2315_;
v___y_2237_ = v___x_2313_;
v___y_2238_ = v___x_2316_;
v___y_2239_ = v_a_2309_;
v___y_2240_ = v_fileName_2304_;
v___y_2241_ = v___y_2301_;
v___y_2242_ = v___y_2302_;
v___y_2243_ = v___y_2233_;
goto v___jp_2235_;
}
}
}
}
v___jp_2326_:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Syntax_getTailPos_x3f(v___y_2328_, v___y_2330_);
lean_dec(v___y_2328_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_inc(v___y_2331_);
v___y_2299_ = v___y_2327_;
v___y_2300_ = v___y_2331_;
v___y_2301_ = v___y_2329_;
v___y_2302_ = v___y_2330_;
v___y_2303_ = v___y_2331_;
goto v___jp_2298_;
}
else
{
lean_object* v_val_2333_; 
v_val_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_val_2333_);
lean_dec_ref(v___x_2332_);
v___y_2299_ = v___y_2327_;
v___y_2300_ = v___y_2331_;
v___y_2301_ = v___y_2329_;
v___y_2302_ = v___y_2330_;
v___y_2303_ = v_val_2333_;
goto v___jp_2298_;
}
}
v___jp_2334_:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Elab_Command_getRef___redArg(v___y_2232_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v_ref_2340_; lean_object* v___x_2341_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v_ref_2340_ = l_Lean_replaceRef(v_ref_2228_, v_a_2339_);
lean_dec(v_a_2339_);
v___x_2341_ = l_Lean_Syntax_getPos_x3f(v_ref_2340_, v___y_2336_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___y_2327_ = v___y_2335_;
v___y_2328_ = v_ref_2340_;
v___y_2329_ = v___y_2337_;
v___y_2330_ = v___y_2336_;
v___y_2331_ = v___x_2342_;
goto v___jp_2326_;
}
else
{
lean_object* v_val_2343_; 
v_val_2343_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_val_2343_);
lean_dec_ref(v___x_2341_);
v___y_2327_ = v___y_2335_;
v___y_2328_ = v_ref_2340_;
v___y_2329_ = v___y_2337_;
v___y_2330_ = v___y_2336_;
v___y_2331_ = v_val_2343_;
goto v___jp_2326_;
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v___y_2232_);
lean_dec_ref(v_msgData_2229_);
v_a_2344_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2338_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2338_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
v___jp_2353_:
{
if (v___y_2356_ == 0)
{
v___y_2335_ = v___y_2354_;
v___y_2336_ = v___y_2355_;
v___y_2337_ = v_severity_2230_;
goto v___jp_2334_;
}
else
{
v___y_2335_ = v___y_2354_;
v___y_2336_ = v___y_2355_;
v___y_2337_ = v___x_2352_;
goto v___jp_2334_;
}
}
v___jp_2357_:
{
if (v___y_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v_scopes_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_opts_2363_; uint8_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2359_ = lean_st_ref_get(v___y_2233_);
v_scopes_2360_ = lean_ctor_get(v___x_2359_, 2);
lean_inc(v_scopes_2360_);
lean_dec(v___x_2359_);
v___x_2361_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2362_ = l_List_head_x21___redArg(v___x_2361_, v_scopes_2360_);
lean_dec(v_scopes_2360_);
v_opts_2363_ = lean_ctor_get(v___x_2362_, 1);
lean_inc_ref(v_opts_2363_);
lean_dec(v___x_2362_);
v___x_2364_ = 1;
v___x_2365_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2230_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_dec_ref(v_opts_2363_);
v___y_2354_ = v___y_2358_;
v___y_2355_ = v___y_2358_;
v___y_2356_ = v___x_2365_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = l_Lean_warningAsError;
v___x_2367_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2363_, v___x_2366_);
lean_dec_ref(v_opts_2363_);
v___y_2354_ = v___y_2358_;
v___y_2355_ = v___y_2358_;
v___y_2356_ = v___x_2367_;
goto v___jp_2353_;
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v___y_2232_);
lean_dec_ref(v_msgData_2229_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2372_, lean_object* v_msgData_2373_, lean_object* v_severity_2374_, lean_object* v_isSilent_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v_severity_boxed_2379_; uint8_t v_isSilent_boxed_2380_; lean_object* v_res_2381_; 
v_severity_boxed_2379_ = lean_unbox(v_severity_2374_);
v_isSilent_boxed_2380_ = lean_unbox(v_isSilent_2375_);
v_res_2381_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2372_, v_msgData_2373_, v_severity_boxed_2379_, v_isSilent_boxed_2380_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec(v_ref_2372_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2382_, lean_object* v_msgData_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = 2;
v___x_2388_ = 0;
lean_inc_ref(v___y_2384_);
v___x_2389_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2382_, v_msgData_2383_, v___x_2387_, v___x_2388_, v___y_2384_, v___y_2385_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2390_, lean_object* v_msgData_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2390_, v_msgData_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v_ref_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2396_, lean_object* v___x_2397_, lean_object* v___x_2398_, lean_object* v_a_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v_it_2402_; lean_object* v_startInclusive_2403_; lean_object* v_endExclusive_2404_; 
if (lean_obj_tag(v_a_2399_) == 0)
{
lean_object* v_currPos_2409_; lean_object* v_searcher_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2439_; 
v_currPos_2409_ = lean_ctor_get(v_a_2399_, 0);
v_searcher_2410_ = lean_ctor_get(v_a_2399_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2412_ = v_a_2399_;
v_isShared_2413_ = v_isSharedCheck_2439_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_searcher_2410_);
lean_inc(v_currPos_2409_);
lean_dec(v_a_2399_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2439_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_str_2414_; lean_object* v_startInclusive_2415_; lean_object* v_endExclusive_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v_str_2414_ = lean_ctor_get(v___x_2397_, 0);
v_startInclusive_2415_ = lean_ctor_get(v___x_2397_, 1);
v_endExclusive_2416_ = lean_ctor_get(v___x_2397_, 2);
v___x_2417_ = lean_nat_sub(v_endExclusive_2416_, v_startInclusive_2415_);
v___x_2418_ = lean_nat_dec_eq(v_searcher_2410_, v___x_2417_);
lean_dec(v___x_2417_);
if (v___x_2418_ == 0)
{
uint32_t v___x_2419_; lean_object* v___x_2420_; uint32_t v___x_2421_; uint8_t v___x_2422_; 
v___x_2419_ = 10;
v___x_2420_ = lean_nat_add(v_startInclusive_2415_, v_searcher_2410_);
v___x_2421_ = lean_string_utf8_get_fast(v_str_2414_, v___x_2420_);
v___x_2422_ = lean_uint32_dec_eq(v___x_2421_, v___x_2419_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_dec(v_searcher_2410_);
v___x_2423_ = lean_string_utf8_next_fast(v_str_2414_, v___x_2420_);
lean_dec(v___x_2420_);
v___x_2424_ = lean_nat_sub(v___x_2423_, v_startInclusive_2415_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2424_);
v___x_2426_ = v___x_2412_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_currPos_2409_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
v_a_2399_ = v___x_2426_;
goto _start;
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_slice_2432_; lean_object* v_nextIt_2434_; 
v___x_2429_ = lean_string_utf8_next_fast(v_str_2414_, v___x_2420_);
v___x_2430_ = lean_nat_sub(v___x_2429_, v___x_2420_);
lean_dec(v___x_2420_);
v___x_2431_ = lean_nat_add(v_searcher_2410_, v___x_2430_);
lean_dec(v___x_2430_);
v_slice_2432_ = l_String_Slice_subslice_x21(v___x_2397_, v_currPos_2409_, v_searcher_2410_);
lean_inc(v___x_2431_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2431_);
lean_ctor_set(v___x_2412_, 0, v___x_2431_);
v_nextIt_2434_ = v___x_2412_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2431_);
v_nextIt_2434_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v_startInclusive_2435_; lean_object* v_endExclusive_2436_; 
v_startInclusive_2435_ = lean_ctor_get(v_slice_2432_, 0);
lean_inc(v_startInclusive_2435_);
v_endExclusive_2436_ = lean_ctor_get(v_slice_2432_, 1);
lean_inc(v_endExclusive_2436_);
lean_dec_ref(v_slice_2432_);
v_it_2402_ = v_nextIt_2434_;
v_startInclusive_2403_ = v_startInclusive_2435_;
v_endExclusive_2404_ = v_endExclusive_2436_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v___x_2438_; 
lean_del_object(v___x_2412_);
lean_dec(v_searcher_2410_);
v___x_2438_ = lean_box(1);
lean_inc(v___x_2398_);
v_it_2402_ = v___x_2438_;
v_startInclusive_2403_ = v_currPos_2409_;
v_endExclusive_2404_ = v___x_2398_;
goto v___jp_2401_;
}
}
}
else
{
lean_dec(v___x_2398_);
lean_dec_ref(v___x_2396_);
return v_b_2400_;
}
v___jp_2401_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_inc_ref(v___x_2396_);
v___x_2405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2396_);
lean_ctor_set(v___x_2405_, 1, v_startInclusive_2403_);
lean_ctor_set(v___x_2405_, 2, v_endExclusive_2404_);
v___x_2406_ = l_String_Slice_toString(v___x_2405_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = lean_array_push(v_b_2400_, v___x_2406_);
v_a_2399_ = v_it_2402_;
v_b_2400_ = v___x_2407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2440_, lean_object* v___x_2441_, lean_object* v___x_2442_, lean_object* v_a_2443_, lean_object* v_b_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2440_, v___x_2441_, v___x_2442_, v_a_2443_, v_b_2444_);
lean_dec_ref(v___x_2441_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2446_, lean_object* v___x_2447_, lean_object* v___x_2448_, lean_object* v_a_2449_, lean_object* v_b_2450_){
_start:
{
lean_object* v_it_2452_; lean_object* v_startInclusive_2453_; lean_object* v_endExclusive_2454_; 
if (lean_obj_tag(v_a_2449_) == 0)
{
lean_object* v_currPos_2459_; lean_object* v_searcher_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2489_; 
v_currPos_2459_ = lean_ctor_get(v_a_2449_, 0);
v_searcher_2460_ = lean_ctor_get(v_a_2449_, 1);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_a_2449_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2462_ = v_a_2449_;
v_isShared_2463_ = v_isSharedCheck_2489_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_searcher_2460_);
lean_inc(v_currPos_2459_);
lean_dec(v_a_2449_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2489_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_str_2464_; lean_object* v_startInclusive_2465_; lean_object* v_endExclusive_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; 
v_str_2464_ = lean_ctor_get(v___x_2447_, 0);
v_startInclusive_2465_ = lean_ctor_get(v___x_2447_, 1);
v_endExclusive_2466_ = lean_ctor_get(v___x_2447_, 2);
v___x_2467_ = lean_nat_sub(v_endExclusive_2466_, v_startInclusive_2465_);
v___x_2468_ = lean_nat_dec_eq(v_searcher_2460_, v___x_2467_);
lean_dec(v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; uint32_t v___x_2470_; uint32_t v___x_2471_; uint8_t v___x_2472_; 
v___x_2469_ = lean_nat_add(v_startInclusive_2465_, v_searcher_2460_);
v___x_2470_ = lean_string_utf8_get_fast(v_str_2464_, v___x_2469_);
v___x_2471_ = 10;
v___x_2472_ = lean_uint32_dec_eq(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_dec(v_searcher_2460_);
v___x_2473_ = lean_string_utf8_next_fast(v_str_2464_, v___x_2469_);
lean_dec(v___x_2469_);
v___x_2474_ = lean_nat_sub(v___x_2473_, v_startInclusive_2465_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2474_);
v___x_2476_ = v___x_2462_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_currPos_2459_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; 
v___x_2477_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2446_, v___x_2447_, v___x_2448_, v___x_2476_, v_b_2450_);
return v___x_2477_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_slice_2482_; lean_object* v_nextIt_2484_; 
v___x_2479_ = lean_string_utf8_next_fast(v_str_2464_, v___x_2469_);
v___x_2480_ = lean_nat_sub(v___x_2479_, v___x_2469_);
lean_dec(v___x_2469_);
v___x_2481_ = lean_nat_add(v_searcher_2460_, v___x_2480_);
lean_dec(v___x_2480_);
v_slice_2482_ = l_String_Slice_subslice_x21(v___x_2447_, v_currPos_2459_, v_searcher_2460_);
lean_inc(v___x_2481_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2481_);
lean_ctor_set(v___x_2462_, 0, v___x_2481_);
v_nextIt_2484_ = v___x_2462_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2481_);
v_nextIt_2484_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v_startInclusive_2485_; lean_object* v_endExclusive_2486_; 
v_startInclusive_2485_ = lean_ctor_get(v_slice_2482_, 0);
lean_inc(v_startInclusive_2485_);
v_endExclusive_2486_ = lean_ctor_get(v_slice_2482_, 1);
lean_inc(v_endExclusive_2486_);
lean_dec_ref(v_slice_2482_);
v_it_2452_ = v_nextIt_2484_;
v_startInclusive_2453_ = v_startInclusive_2485_;
v_endExclusive_2454_ = v_endExclusive_2486_;
goto v___jp_2451_;
}
}
}
else
{
lean_object* v___x_2488_; 
lean_del_object(v___x_2462_);
lean_dec(v_searcher_2460_);
v___x_2488_ = lean_box(1);
lean_inc(v___x_2448_);
v_it_2452_ = v___x_2488_;
v_startInclusive_2453_ = v_currPos_2459_;
v_endExclusive_2454_ = v___x_2448_;
goto v___jp_2451_;
}
}
}
else
{
lean_dec(v___x_2448_);
lean_dec_ref(v___x_2446_);
return v_b_2450_;
}
v___jp_2451_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_inc_ref(v___x_2446_);
v___x_2455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2446_);
lean_ctor_set(v___x_2455_, 1, v_startInclusive_2453_);
lean_ctor_set(v___x_2455_, 2, v_endExclusive_2454_);
v___x_2456_ = l_String_Slice_toString(v___x_2455_);
lean_dec_ref(v___x_2455_);
v___x_2457_ = lean_array_push(v_b_2450_, v___x_2456_);
v___x_2458_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2446_, v___x_2447_, v___x_2448_, v_it_2452_, v___x_2457_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2490_, lean_object* v___x_2491_, lean_object* v___x_2492_, lean_object* v_a_2493_, lean_object* v_b_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2490_, v___x_2491_, v___x_2492_, v_a_2493_, v_b_2494_);
lean_dec_ref(v___x_2491_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v_infoState_2500_; uint8_t v_enabled_2501_; 
v___x_2499_ = lean_st_ref_get(v___y_2497_);
v_infoState_2500_ = lean_ctor_get(v___x_2499_, 8);
lean_inc_ref(v_infoState_2500_);
lean_dec(v___x_2499_);
v_enabled_2501_ = lean_ctor_get_uint8(v_infoState_2500_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2500_);
if (v_enabled_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec_ref(v_t_2496_);
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; lean_object* v_infoState_2505_; lean_object* v_env_2506_; lean_object* v_messages_2507_; lean_object* v_scopes_2508_; lean_object* v_usedQuotCtxts_2509_; lean_object* v_nextMacroScope_2510_; lean_object* v_maxRecDepth_2511_; lean_object* v_ngen_2512_; lean_object* v_auxDeclNGen_2513_; lean_object* v_traceState_2514_; lean_object* v_snapshotTasks_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2537_; 
v___x_2504_ = lean_st_ref_take(v___y_2497_);
v_infoState_2505_ = lean_ctor_get(v___x_2504_, 8);
v_env_2506_ = lean_ctor_get(v___x_2504_, 0);
v_messages_2507_ = lean_ctor_get(v___x_2504_, 1);
v_scopes_2508_ = lean_ctor_get(v___x_2504_, 2);
v_usedQuotCtxts_2509_ = lean_ctor_get(v___x_2504_, 3);
v_nextMacroScope_2510_ = lean_ctor_get(v___x_2504_, 4);
v_maxRecDepth_2511_ = lean_ctor_get(v___x_2504_, 5);
v_ngen_2512_ = lean_ctor_get(v___x_2504_, 6);
v_auxDeclNGen_2513_ = lean_ctor_get(v___x_2504_, 7);
v_traceState_2514_ = lean_ctor_get(v___x_2504_, 9);
v_snapshotTasks_2515_ = lean_ctor_get(v___x_2504_, 10);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2517_ = v___x_2504_;
v_isShared_2518_ = v_isSharedCheck_2537_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_snapshotTasks_2515_);
lean_inc(v_traceState_2514_);
lean_inc(v_infoState_2505_);
lean_inc(v_auxDeclNGen_2513_);
lean_inc(v_ngen_2512_);
lean_inc(v_maxRecDepth_2511_);
lean_inc(v_nextMacroScope_2510_);
lean_inc(v_usedQuotCtxts_2509_);
lean_inc(v_scopes_2508_);
lean_inc(v_messages_2507_);
lean_inc(v_env_2506_);
lean_dec(v___x_2504_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2537_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
uint8_t v_enabled_2519_; lean_object* v_assignment_2520_; lean_object* v_lazyAssignment_2521_; lean_object* v_trees_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2536_; 
v_enabled_2519_ = lean_ctor_get_uint8(v_infoState_2505_, sizeof(void*)*3);
v_assignment_2520_ = lean_ctor_get(v_infoState_2505_, 0);
v_lazyAssignment_2521_ = lean_ctor_get(v_infoState_2505_, 1);
v_trees_2522_ = lean_ctor_get(v_infoState_2505_, 2);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_infoState_2505_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2524_ = v_infoState_2505_;
v_isShared_2525_ = v_isSharedCheck_2536_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_trees_2522_);
lean_inc(v_lazyAssignment_2521_);
lean_inc(v_assignment_2520_);
lean_dec(v_infoState_2505_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2536_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = l_Lean_PersistentArray_push___redArg(v_trees_2522_, v_t_2496_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 2, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_assignment_2520_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_lazyAssignment_2521_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v___x_2526_);
lean_ctor_set_uint8(v_reuseFailAlloc_2535_, sizeof(void*)*3, v_enabled_2519_);
v___x_2528_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 8, v___x_2528_);
v___x_2530_ = v___x_2517_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_env_2506_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_messages_2507_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_scopes_2508_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_usedQuotCtxts_2509_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_nextMacroScope_2510_);
lean_ctor_set(v_reuseFailAlloc_2534_, 5, v_maxRecDepth_2511_);
lean_ctor_set(v_reuseFailAlloc_2534_, 6, v_ngen_2512_);
lean_ctor_set(v_reuseFailAlloc_2534_, 7, v_auxDeclNGen_2513_);
lean_ctor_set(v_reuseFailAlloc_2534_, 8, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2534_, 9, v_traceState_2514_);
lean_ctor_set(v_reuseFailAlloc_2534_, 10, v_snapshotTasks_2515_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_st_ref_set(v___y_2497_, v___x_2530_);
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2538_, v___y_2539_);
lean_dec(v___y_2539_);
return v_res_2541_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(32u);
v___x_2543_ = lean_mk_empty_array_with_capacity(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2545_ = ((size_t)5ULL);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
lean_ctor_set(v___x_2550_, 2, v___x_2546_);
lean_ctor_set(v___x_2550_, 3, v___x_2546_);
lean_ctor_set_usize(v___x_2550_, 4, v___x_2545_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; lean_object* v_infoState_2556_; uint8_t v_enabled_2557_; 
v___x_2555_ = lean_st_ref_get(v___y_2553_);
v_infoState_2556_ = lean_ctor_get(v___x_2555_, 8);
lean_inc_ref(v_infoState_2556_);
lean_dec(v___x_2555_);
v_enabled_2557_ = lean_ctor_get_uint8(v_infoState_2556_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2556_);
if (v_enabled_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec_ref(v_t_2551_);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_t_2551_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2561_, v___y_2553_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_2568_, lean_object* v_edited_2569_, lean_object* v_b_2570_){
_start:
{
lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2591_; 
v_fst_2571_ = lean_ctor_get(v_b_2570_, 0);
v_snd_2572_ = lean_ctor_get(v_b_2570_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_b_2570_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2574_ = v_b_2570_;
v_isShared_2575_ = v_isSharedCheck_2591_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snd_2572_);
lean_inc(v_fst_2571_);
lean_dec(v_b_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2591_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
uint8_t v___x_2576_; 
v___x_2576_ = lean_nat_dec_lt(v_snd_2572_, v___x_2568_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2578_; 
if (v_isShared_2575_ == 0)
{
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_fst_2571_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_snd_2572_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
else
{
uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2580_ = 0;
v___x_2581_ = lean_array_fget_borrowed(v_edited_2569_, v_snd_2572_);
v___x_2582_ = lean_box(v___x_2580_);
lean_inc(v___x_2581_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v___x_2581_);
lean_ctor_set(v___x_2574_, 0, v___x_2582_);
v___x_2584_ = v___x_2574_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2581_);
v___x_2584_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2585_ = lean_array_push(v_fst_2571_, v___x_2584_);
v___x_2586_ = lean_unsigned_to_nat(1u);
v___x_2587_ = lean_nat_add(v_snd_2572_, v___x_2586_);
lean_dec(v_snd_2572_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2585_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v_b_2570_ = v___x_2588_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_2592_, lean_object* v_edited_2593_, lean_object* v_b_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_2592_, v_edited_2593_, v_b_2594_);
lean_dec_ref(v_edited_2593_);
lean_dec(v___x_2592_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_inst_2596_, lean_object* v_edited_2597_, lean_object* v___x_2598_, lean_object* v_a_2599_, lean_object* v_b_2600_){
_start:
{
lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2626_; 
v_fst_2601_ = lean_ctor_get(v_b_2600_, 0);
v_snd_2602_ = lean_ctor_get(v_b_2600_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_b_2600_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2604_ = v_b_2600_;
v_isShared_2605_ = v_isSharedCheck_2626_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_inc(v_fst_2601_);
lean_dec(v_b_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2626_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
uint8_t v___y_2607_; uint8_t v___x_2622_; 
v___x_2622_ = lean_nat_dec_lt(v_snd_2602_, v___x_2598_);
if (v___x_2622_ == 0)
{
v___y_2607_ = v___x_2622_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
lean_inc_ref(v_inst_2596_);
v___x_2623_ = lean_array_get_borrowed(v_inst_2596_, v_edited_2597_, v_snd_2602_);
v___x_2624_ = lean_string_dec_eq(v___x_2623_, v_a_2599_);
if (v___x_2624_ == 0)
{
v___y_2607_ = v___x_2622_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2625_; 
lean_del_object(v___x_2604_);
lean_dec_ref(v_inst_2596_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_fst_2601_);
lean_ctor_set(v___x_2625_, 1, v_snd_2602_);
return v___x_2625_;
}
}
v___jp_2606_:
{
if (v___y_2607_ == 0)
{
lean_object* v___x_2609_; 
lean_dec_ref(v_inst_2596_);
if (v_isShared_2605_ == 0)
{
v___x_2609_ = v___x_2604_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_fst_2601_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_snd_2602_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
else
{
uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2611_ = 0;
lean_inc_ref(v_inst_2596_);
v___x_2612_ = lean_array_get_borrowed(v_inst_2596_, v_edited_2597_, v_snd_2602_);
v___x_2613_ = lean_box(v___x_2611_);
lean_inc(v___x_2612_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___x_2612_);
lean_ctor_set(v___x_2604_, 0, v___x_2613_);
v___x_2615_ = v___x_2604_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___x_2612_);
v___x_2615_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2616_ = lean_array_push(v_fst_2601_, v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_add(v_snd_2602_, v___x_2617_);
lean_dec(v_snd_2602_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2616_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v_b_2600_ = v___x_2619_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_inst_2627_, lean_object* v_edited_2628_, lean_object* v___x_2629_, lean_object* v_a_2630_, lean_object* v_b_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_inst_2627_, v_edited_2628_, v___x_2629_, v_a_2630_, v_b_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v___x_2629_);
lean_dec_ref(v_edited_2628_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_inst_2633_, lean_object* v_original_2634_, lean_object* v___x_2635_, lean_object* v_a_2636_, lean_object* v_b_2637_){
_start:
{
lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2663_; 
v_fst_2638_ = lean_ctor_get(v_b_2637_, 0);
v_snd_2639_ = lean_ctor_get(v_b_2637_, 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_b_2637_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2641_ = v_b_2637_;
v_isShared_2642_ = v_isSharedCheck_2663_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snd_2639_);
lean_inc(v_fst_2638_);
lean_dec(v_b_2637_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2663_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
uint8_t v___y_2644_; uint8_t v___x_2659_; 
v___x_2659_ = lean_nat_dec_lt(v_snd_2639_, v___x_2635_);
if (v___x_2659_ == 0)
{
v___y_2644_ = v___x_2659_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
lean_inc_ref(v_inst_2633_);
v___x_2660_ = lean_array_get_borrowed(v_inst_2633_, v_original_2634_, v_snd_2639_);
v___x_2661_ = lean_string_dec_eq(v___x_2660_, v_a_2636_);
if (v___x_2661_ == 0)
{
v___y_2644_ = v___x_2659_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2662_; 
lean_del_object(v___x_2641_);
lean_dec_ref(v_inst_2633_);
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v_fst_2638_);
lean_ctor_set(v___x_2662_, 1, v_snd_2639_);
return v___x_2662_;
}
}
v___jp_2643_:
{
if (v___y_2644_ == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref(v_inst_2633_);
if (v_isShared_2642_ == 0)
{
v___x_2646_ = v___x_2641_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_fst_2638_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_snd_2639_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2648_ = 1;
lean_inc_ref(v_inst_2633_);
v___x_2649_ = lean_array_get_borrowed(v_inst_2633_, v_original_2634_, v_snd_2639_);
v___x_2650_ = lean_box(v___x_2648_);
lean_inc(v___x_2649_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v___x_2649_);
lean_ctor_set(v___x_2641_, 0, v___x_2650_);
v___x_2652_ = v___x_2641_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___x_2649_);
v___x_2652_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = lean_array_push(v_fst_2638_, v___x_2652_);
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = lean_nat_add(v_snd_2639_, v___x_2654_);
lean_dec(v_snd_2639_);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v_b_2637_ = v___x_2656_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_inst_2664_, lean_object* v_original_2665_, lean_object* v___x_2666_, lean_object* v_a_2667_, lean_object* v_b_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_inst_2664_, v_original_2665_, v___x_2666_, v_a_2667_, v_b_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v___x_2666_);
lean_dec_ref(v_original_2665_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_inst_2670_, lean_object* v_original_2671_, lean_object* v___x_2672_, lean_object* v_edited_2673_, lean_object* v___x_2674_, lean_object* v_as_2675_, size_t v_sz_2676_, size_t v_i_2677_, lean_object* v_b_2678_){
_start:
{
uint8_t v___x_2679_; 
v___x_2679_ = lean_usize_dec_lt(v_i_2677_, v_sz_2676_);
if (v___x_2679_ == 0)
{
lean_dec_ref(v_inst_2670_);
return v_b_2678_;
}
else
{
lean_object* v_snd_2680_; lean_object* v_fst_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2728_; 
v_snd_2680_ = lean_ctor_get(v_b_2678_, 1);
v_fst_2681_ = lean_ctor_get(v_b_2678_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_b_2678_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2683_ = v_b_2678_;
v_isShared_2684_ = v_isSharedCheck_2728_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2680_);
lean_inc(v_fst_2681_);
lean_dec(v_b_2678_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2728_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2727_; 
v_fst_2685_ = lean_ctor_get(v_snd_2680_, 0);
v_snd_2686_ = lean_ctor_get(v_snd_2680_, 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_snd_2680_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2688_ = v_snd_2680_;
v_isShared_2689_ = v_isSharedCheck_2727_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_snd_2686_);
lean_inc(v_fst_2685_);
lean_dec(v_snd_2680_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2727_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_a_2690_; lean_object* v___x_2692_; 
v_a_2690_ = lean_array_uget_borrowed(v_as_2675_, v_i_2677_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v_fst_2685_);
lean_ctor_set(v___x_2688_, 0, v_fst_2681_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_fst_2681_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_fst_2685_);
v___x_2692_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2725_; 
lean_inc_ref(v_inst_2670_);
v___x_2693_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_inst_2670_, v_original_2671_, v___x_2672_, v_a_2690_, v___x_2692_);
v_fst_2694_ = lean_ctor_get(v___x_2693_, 0);
v_snd_2695_ = lean_ctor_get(v___x_2693_, 1);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2697_ = v___x_2693_;
v_isShared_2698_ = v_isSharedCheck_2725_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_inc(v_fst_2694_);
lean_dec(v___x_2693_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2725_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v_snd_2686_);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_fst_2694_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_snd_2686_);
v___x_2700_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v_fst_2702_; lean_object* v_snd_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2723_; 
lean_inc_ref(v_inst_2670_);
v___x_2701_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_inst_2670_, v_edited_2673_, v___x_2674_, v_a_2690_, v___x_2700_);
v_fst_2702_ = lean_ctor_get(v___x_2701_, 0);
v_snd_2703_ = lean_ctor_get(v___x_2701_, 1);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2723_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snd_2703_);
lean_inc(v_fst_2702_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2723_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2707_ = 2;
v___x_2708_ = lean_box(v___x_2707_);
lean_inc(v_a_2690_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v_a_2690_);
lean_ctor_set(v___x_2705_, 0, v___x_2708_);
v___x_2710_ = v___x_2705_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_a_2690_);
v___x_2710_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2711_ = lean_array_push(v_fst_2702_, v___x_2710_);
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = lean_nat_add(v_snd_2695_, v___x_2712_);
lean_dec(v_snd_2695_);
v___x_2714_ = lean_nat_add(v_snd_2703_, v___x_2712_);
lean_dec(v_snd_2703_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2714_);
lean_ctor_set(v___x_2683_, 0, v___x_2713_);
v___x_2716_ = v___x_2683_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; 
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2711_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = ((size_t)1ULL);
v___x_2719_ = lean_usize_add(v_i_2677_, v___x_2718_);
v_i_2677_ = v___x_2719_;
v_b_2678_ = v___x_2717_;
goto _start;
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_inst_2729_, lean_object* v_original_2730_, lean_object* v___x_2731_, lean_object* v_edited_2732_, lean_object* v___x_2733_, lean_object* v_as_2734_, lean_object* v_sz_2735_, lean_object* v_i_2736_, lean_object* v_b_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2735_);
lean_dec(v_sz_2735_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2736_);
lean_dec(v_i_2736_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_inst_2729_, v_original_2730_, v___x_2731_, v_edited_2732_, v___x_2733_, v_as_2734_, v_sz_boxed_2738_, v_i_boxed_2739_, v_b_2737_);
lean_dec_ref(v_as_2734_);
lean_dec(v___x_2733_);
lean_dec_ref(v_edited_2732_);
lean_dec(v___x_2731_);
lean_dec_ref(v_original_2730_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_inst_2741_, lean_object* v_edited_2742_, lean_object* v___x_2743_, lean_object* v_original_2744_, lean_object* v___x_2745_, lean_object* v_as_2746_, size_t v_sz_2747_, size_t v_i_2748_, lean_object* v_b_2749_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_lt(v_i_2748_, v_sz_2747_);
if (v___x_2750_ == 0)
{
lean_dec_ref(v_inst_2741_);
return v_b_2749_;
}
else
{
lean_object* v_snd_2751_; lean_object* v_fst_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2799_; 
v_snd_2751_ = lean_ctor_get(v_b_2749_, 1);
v_fst_2752_ = lean_ctor_get(v_b_2749_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_b_2749_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2754_ = v_b_2749_;
v_isShared_2755_ = v_isSharedCheck_2799_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_snd_2751_);
lean_inc(v_fst_2752_);
lean_dec(v_b_2749_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2799_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2798_; 
v_fst_2756_ = lean_ctor_get(v_snd_2751_, 0);
v_snd_2757_ = lean_ctor_get(v_snd_2751_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_snd_2751_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2759_ = v_snd_2751_;
v_isShared_2760_ = v_isSharedCheck_2798_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_inc(v_fst_2756_);
lean_dec(v_snd_2751_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2798_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v_a_2761_; lean_object* v___x_2763_; 
v_a_2761_ = lean_array_uget_borrowed(v_as_2746_, v_i_2748_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v_fst_2756_);
lean_ctor_set(v___x_2759_, 0, v_fst_2752_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_fst_2752_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_fst_2756_);
v___x_2763_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2796_; 
lean_inc_ref(v_inst_2741_);
v___x_2764_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_inst_2741_, v_original_2744_, v___x_2745_, v_a_2761_, v___x_2763_);
v_fst_2765_ = lean_ctor_get(v___x_2764_, 0);
v_snd_2766_ = lean_ctor_get(v___x_2764_, 1);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2768_ = v___x_2764_;
v_isShared_2769_ = v_isSharedCheck_2796_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_snd_2766_);
lean_inc(v_fst_2765_);
lean_dec(v___x_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2796_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v_snd_2757_);
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_fst_2765_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_snd_2757_);
v___x_2771_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; lean_object* v_fst_2773_; lean_object* v_snd_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2794_; 
lean_inc_ref(v_inst_2741_);
v___x_2772_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_inst_2741_, v_edited_2742_, v___x_2743_, v_a_2761_, v___x_2771_);
v_fst_2773_ = lean_ctor_get(v___x_2772_, 0);
v_snd_2774_ = lean_ctor_get(v___x_2772_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2776_ = v___x_2772_;
v_isShared_2777_ = v_isSharedCheck_2794_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_snd_2774_);
lean_inc(v_fst_2773_);
lean_dec(v___x_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2794_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = 2;
v___x_2779_ = lean_box(v___x_2778_);
lean_inc(v_a_2761_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v_a_2761_);
lean_ctor_set(v___x_2776_, 0, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2761_);
v___x_2781_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2782_ = lean_array_push(v_fst_2773_, v___x_2781_);
v___x_2783_ = lean_unsigned_to_nat(1u);
v___x_2784_ = lean_nat_add(v_snd_2766_, v___x_2783_);
lean_dec(v_snd_2766_);
v___x_2785_ = lean_nat_add(v_snd_2774_, v___x_2783_);
lean_dec(v_snd_2774_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v___x_2785_);
lean_ctor_set(v___x_2754_, 0, v___x_2784_);
v___x_2787_ = v___x_2754_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; size_t v___x_2789_; size_t v___x_2790_; lean_object* v___x_2791_; 
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2782_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = ((size_t)1ULL);
v___x_2790_ = lean_usize_add(v_i_2748_, v___x_2789_);
v___x_2791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_inst_2741_, v_original_2744_, v___x_2745_, v_edited_2742_, v___x_2743_, v_as_2746_, v_sz_2747_, v___x_2790_, v___x_2788_);
return v___x_2791_;
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_inst_2800_, lean_object* v_edited_2801_, lean_object* v___x_2802_, lean_object* v_original_2803_, lean_object* v___x_2804_, lean_object* v_as_2805_, lean_object* v_sz_2806_, lean_object* v_i_2807_, lean_object* v_b_2808_){
_start:
{
size_t v_sz_boxed_2809_; size_t v_i_boxed_2810_; lean_object* v_res_2811_; 
v_sz_boxed_2809_ = lean_unbox_usize(v_sz_2806_);
lean_dec(v_sz_2806_);
v_i_boxed_2810_ = lean_unbox_usize(v_i_2807_);
lean_dec(v_i_2807_);
v_res_2811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_inst_2800_, v_edited_2801_, v___x_2802_, v_original_2803_, v___x_2804_, v_as_2805_, v_sz_boxed_2809_, v_i_boxed_2810_, v_b_2808_);
lean_dec_ref(v_as_2805_);
lean_dec(v___x_2804_);
lean_dec_ref(v_original_2803_);
lean_dec(v___x_2802_);
lean_dec_ref(v_edited_2801_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2812_, lean_object* v_x_2813_){
_start:
{
if (lean_obj_tag(v_x_2813_) == 0)
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_box(0);
return v___x_2814_;
}
else
{
lean_object* v_key_2815_; lean_object* v_value_2816_; lean_object* v_tail_2817_; uint8_t v___x_2818_; 
v_key_2815_ = lean_ctor_get(v_x_2813_, 0);
v_value_2816_ = lean_ctor_get(v_x_2813_, 1);
v_tail_2817_ = lean_ctor_get(v_x_2813_, 2);
v___x_2818_ = lean_string_dec_eq(v_key_2815_, v_a_2812_);
if (v___x_2818_ == 0)
{
v_x_2813_ = v_tail_2817_;
goto _start;
}
else
{
lean_object* v___x_2820_; 
lean_inc(v_value_2816_);
v___x_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2820_, 0, v_value_2816_);
return v___x_2820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2821_, v_x_2822_);
lean_dec(v_x_2822_);
lean_dec_ref(v_a_2821_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_buckets_2826_; lean_object* v___x_2827_; uint64_t v___x_2828_; uint64_t v___x_2829_; uint64_t v___x_2830_; uint64_t v_fold_2831_; uint64_t v___x_2832_; uint64_t v___x_2833_; uint64_t v___x_2834_; size_t v___x_2835_; size_t v___x_2836_; size_t v___x_2837_; size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_buckets_2826_ = lean_ctor_get(v_m_2824_, 1);
v___x_2827_ = lean_array_get_size(v_buckets_2826_);
v___x_2828_ = lean_string_hash(v_a_2825_);
v___x_2829_ = 32ULL;
v___x_2830_ = lean_uint64_shift_right(v___x_2828_, v___x_2829_);
v_fold_2831_ = lean_uint64_xor(v___x_2828_, v___x_2830_);
v___x_2832_ = 16ULL;
v___x_2833_ = lean_uint64_shift_right(v_fold_2831_, v___x_2832_);
v___x_2834_ = lean_uint64_xor(v_fold_2831_, v___x_2833_);
v___x_2835_ = lean_uint64_to_usize(v___x_2834_);
v___x_2836_ = lean_usize_of_nat(v___x_2827_);
v___x_2837_ = ((size_t)1ULL);
v___x_2838_ = lean_usize_sub(v___x_2836_, v___x_2837_);
v___x_2839_ = lean_usize_land(v___x_2835_, v___x_2838_);
v___x_2840_ = lean_array_uget_borrowed(v_buckets_2826_, v___x_2839_);
v___x_2841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2825_, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2842_, v_a_2843_);
lean_dec_ref(v_a_2843_);
lean_dec_ref(v_m_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2845_, lean_object* v_b_2846_, lean_object* v_x_2847_){
_start:
{
if (lean_obj_tag(v_x_2847_) == 0)
{
lean_dec(v_b_2846_);
lean_dec_ref(v_a_2845_);
return v_x_2847_;
}
else
{
lean_object* v_key_2848_; lean_object* v_value_2849_; lean_object* v_tail_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2862_; 
v_key_2848_ = lean_ctor_get(v_x_2847_, 0);
v_value_2849_ = lean_ctor_get(v_x_2847_, 1);
v_tail_2850_ = lean_ctor_get(v_x_2847_, 2);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_x_2847_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2852_ = v_x_2847_;
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_tail_2850_);
lean_inc(v_value_2849_);
lean_inc(v_key_2848_);
lean_dec(v_x_2847_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_string_dec_eq(v_key_2848_, v_a_2845_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2845_, v_b_2846_, v_tail_2850_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 2, v___x_2855_);
v___x_2857_ = v___x_2852_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_key_2848_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_value_2849_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
else
{
lean_object* v___x_2860_; 
lean_dec(v_value_2849_);
lean_dec(v_key_2848_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 1, v_b_2846_);
lean_ctor_set(v___x_2852_, 0, v_a_2845_);
v___x_2860_ = v___x_2852_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2845_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_b_2846_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_tail_2850_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2863_, lean_object* v_x_2864_){
_start:
{
if (lean_obj_tag(v_x_2864_) == 0)
{
uint8_t v___x_2865_; 
v___x_2865_ = 0;
return v___x_2865_;
}
else
{
lean_object* v_key_2866_; lean_object* v_tail_2867_; uint8_t v___x_2868_; 
v_key_2866_ = lean_ctor_get(v_x_2864_, 0);
v_tail_2867_ = lean_ctor_get(v_x_2864_, 2);
v___x_2868_ = lean_string_dec_eq(v_key_2866_, v_a_2863_);
if (v___x_2868_ == 0)
{
v_x_2864_ = v_tail_2867_;
goto _start;
}
else
{
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2870_, lean_object* v_x_2871_){
_start:
{
uint8_t v_res_2872_; lean_object* v_r_2873_; 
v_res_2872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2870_, v_x_2871_);
lean_dec(v_x_2871_);
lean_dec_ref(v_a_2870_);
v_r_2873_ = lean_box(v_res_2872_);
return v_r_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
return v_x_2874_;
}
else
{
lean_object* v_key_2876_; lean_object* v_value_2877_; lean_object* v_tail_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2901_; 
v_key_2876_ = lean_ctor_get(v_x_2875_, 0);
v_value_2877_ = lean_ctor_get(v_x_2875_, 1);
v_tail_2878_ = lean_ctor_get(v_x_2875_, 2);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_x_2875_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2880_ = v_x_2875_;
v_isShared_2881_ = v_isSharedCheck_2901_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_tail_2878_);
lean_inc(v_value_2877_);
lean_inc(v_key_2876_);
lean_dec(v_x_2875_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2901_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; uint64_t v___x_2883_; uint64_t v___x_2884_; uint64_t v___x_2885_; uint64_t v_fold_2886_; uint64_t v___x_2887_; uint64_t v___x_2888_; uint64_t v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2882_ = lean_array_get_size(v_x_2874_);
v___x_2883_ = lean_string_hash(v_key_2876_);
v___x_2884_ = 32ULL;
v___x_2885_ = lean_uint64_shift_right(v___x_2883_, v___x_2884_);
v_fold_2886_ = lean_uint64_xor(v___x_2883_, v___x_2885_);
v___x_2887_ = 16ULL;
v___x_2888_ = lean_uint64_shift_right(v_fold_2886_, v___x_2887_);
v___x_2889_ = lean_uint64_xor(v_fold_2886_, v___x_2888_);
v___x_2890_ = lean_uint64_to_usize(v___x_2889_);
v___x_2891_ = lean_usize_of_nat(v___x_2882_);
v___x_2892_ = ((size_t)1ULL);
v___x_2893_ = lean_usize_sub(v___x_2891_, v___x_2892_);
v___x_2894_ = lean_usize_land(v___x_2890_, v___x_2893_);
v___x_2895_ = lean_array_uget_borrowed(v_x_2874_, v___x_2894_);
lean_inc(v___x_2895_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 2, v___x_2895_);
v___x_2897_ = v___x_2880_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_key_2876_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_value_2877_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_array_uset(v_x_2874_, v___x_2894_, v___x_2897_);
v_x_2874_ = v___x_2898_;
v_x_2875_ = v_tail_2878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2902_, lean_object* v_source_2903_, lean_object* v_target_2904_){
_start:
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_array_get_size(v_source_2903_);
v___x_2906_ = lean_nat_dec_lt(v_i_2902_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec_ref(v_source_2903_);
lean_dec(v_i_2902_);
return v_target_2904_;
}
else
{
lean_object* v_es_2907_; lean_object* v___x_2908_; lean_object* v_source_2909_; lean_object* v_target_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_es_2907_ = lean_array_fget(v_source_2903_, v_i_2902_);
v___x_2908_ = lean_box(0);
v_source_2909_ = lean_array_fset(v_source_2903_, v_i_2902_, v___x_2908_);
v_target_2910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2904_, v_es_2907_);
v___x_2911_ = lean_unsigned_to_nat(1u);
v___x_2912_ = lean_nat_add(v_i_2902_, v___x_2911_);
lean_dec(v_i_2902_);
v_i_2902_ = v___x_2912_;
v_source_2903_ = v_source_2909_;
v_target_2904_ = v_target_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2914_){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v_nbuckets_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2915_ = lean_array_get_size(v_data_2914_);
v___x_2916_ = lean_unsigned_to_nat(2u);
v_nbuckets_2917_ = lean_nat_mul(v___x_2915_, v___x_2916_);
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_mk_array(v_nbuckets_2917_, v___x_2919_);
v___x_2921_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2918_, v_data_2914_, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2922_, lean_object* v_a_2923_, lean_object* v_b_2924_){
_start:
{
lean_object* v_size_2925_; lean_object* v_buckets_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2969_; 
v_size_2925_ = lean_ctor_get(v_m_2922_, 0);
v_buckets_2926_ = lean_ctor_get(v_m_2922_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_m_2922_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2928_ = v_m_2922_;
v_isShared_2929_ = v_isSharedCheck_2969_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_buckets_2926_);
lean_inc(v_size_2925_);
lean_dec(v_m_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2969_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; uint64_t v___x_2931_; uint64_t v___x_2932_; uint64_t v___x_2933_; uint64_t v_fold_2934_; uint64_t v___x_2935_; uint64_t v___x_2936_; uint64_t v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; size_t v___x_2940_; size_t v___x_2941_; size_t v___x_2942_; lean_object* v_bkt_2943_; uint8_t v___x_2944_; 
v___x_2930_ = lean_array_get_size(v_buckets_2926_);
v___x_2931_ = lean_string_hash(v_a_2923_);
v___x_2932_ = 32ULL;
v___x_2933_ = lean_uint64_shift_right(v___x_2931_, v___x_2932_);
v_fold_2934_ = lean_uint64_xor(v___x_2931_, v___x_2933_);
v___x_2935_ = 16ULL;
v___x_2936_ = lean_uint64_shift_right(v_fold_2934_, v___x_2935_);
v___x_2937_ = lean_uint64_xor(v_fold_2934_, v___x_2936_);
v___x_2938_ = lean_uint64_to_usize(v___x_2937_);
v___x_2939_ = lean_usize_of_nat(v___x_2930_);
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_sub(v___x_2939_, v___x_2940_);
v___x_2942_ = lean_usize_land(v___x_2938_, v___x_2941_);
v_bkt_2943_ = lean_array_uget_borrowed(v_buckets_2926_, v___x_2942_);
v___x_2944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2923_, v_bkt_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v_size_x27_2946_; lean_object* v___x_2947_; lean_object* v_buckets_x27_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2945_ = lean_unsigned_to_nat(1u);
v_size_x27_2946_ = lean_nat_add(v_size_2925_, v___x_2945_);
lean_dec(v_size_2925_);
lean_inc(v_bkt_2943_);
v___x_2947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2947_, 0, v_a_2923_);
lean_ctor_set(v___x_2947_, 1, v_b_2924_);
lean_ctor_set(v___x_2947_, 2, v_bkt_2943_);
v_buckets_x27_2948_ = lean_array_uset(v_buckets_2926_, v___x_2942_, v___x_2947_);
v___x_2949_ = lean_unsigned_to_nat(4u);
v___x_2950_ = lean_nat_mul(v_size_x27_2946_, v___x_2949_);
v___x_2951_ = lean_unsigned_to_nat(3u);
v___x_2952_ = lean_nat_div(v___x_2950_, v___x_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_array_get_size(v_buckets_x27_2948_);
v___x_2954_ = lean_nat_dec_le(v___x_2952_, v___x_2953_);
lean_dec(v___x_2952_);
if (v___x_2954_ == 0)
{
lean_object* v_val_2955_; lean_object* v___x_2957_; 
v_val_2955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_2948_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v_val_2955_);
lean_ctor_set(v___x_2928_, 0, v_size_x27_2946_);
v___x_2957_ = v___x_2928_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_size_x27_2946_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_val_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
else
{
lean_object* v___x_2960_; 
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v_buckets_x27_2948_);
lean_ctor_set(v___x_2928_, 0, v_size_x27_2946_);
v___x_2960_ = v___x_2928_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_size_x27_2946_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_buckets_x27_2948_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
lean_object* v___x_2962_; lean_object* v_buckets_x27_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_inc(v_bkt_2943_);
v___x_2962_ = lean_box(0);
v_buckets_x27_2963_ = lean_array_uset(v_buckets_2926_, v___x_2942_, v___x_2962_);
v___x_2964_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2923_, v_b_2924_, v_bkt_2943_);
v___x_2965_ = lean_array_uset(v_buckets_x27_2963_, v___x_2942_, v___x_2964_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v___x_2965_);
v___x_2967_ = v___x_2928_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_size_2925_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2965_);
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
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_2970_, lean_object* v_index_2971_, lean_object* v_val_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_2970_, v_val_2972_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2974_ = lean_unsigned_to_nat(1u);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_index_2971_);
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2974_);
lean_ctor_set(v___x_2978_, 1, v___x_2975_);
lean_ctor_set(v___x_2978_, 2, v___x_2976_);
lean_ctor_set(v___x_2978_, 3, v___x_2977_);
v___x_2979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2970_, v_val_2972_, v___x_2978_);
return v___x_2979_;
}
else
{
lean_object* v_val_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3001_; 
v_val_2980_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2982_ = v___x_2973_;
v_isShared_2983_ = v_isSharedCheck_3001_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_val_2980_);
lean_dec(v___x_2973_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3001_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v_leftCount_2984_; lean_object* v_rightCount_2985_; lean_object* v_rightIndex_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2999_; 
v_leftCount_2984_ = lean_ctor_get(v_val_2980_, 0);
v_rightCount_2985_ = lean_ctor_get(v_val_2980_, 2);
v_rightIndex_2986_ = lean_ctor_get(v_val_2980_, 3);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_val_2980_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v_val_2980_, 1);
lean_dec(v_unused_3000_);
v___x_2988_ = v_val_2980_;
v_isShared_2989_ = v_isSharedCheck_2999_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_rightIndex_2986_);
lean_inc(v_rightCount_2985_);
lean_inc(v_leftCount_2984_);
lean_dec(v_val_2980_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2999_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = lean_nat_add(v_leftCount_2984_, v___x_2990_);
lean_dec(v_leftCount_2984_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_index_2971_);
v___x_2993_ = v___x_2982_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_index_2971_);
v___x_2993_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_2993_);
lean_ctor_set(v___x_2988_, 0, v___x_2991_);
v___x_2995_ = v___x_2988_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_rightCount_2985_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v_rightIndex_2986_);
v___x_2995_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2970_, v_val_2972_, v___x_2995_);
return v___x_2996_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3002_, lean_object* v_fst_3003_, lean_object* v___x_3004_, lean_object* v_fst_3005_, lean_object* v_a_3006_, lean_object* v_b_3007_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_nat_dec_lt(v_a_3006_, v_upperBound_3002_);
if (v___x_3008_ == 0)
{
lean_dec(v_a_3006_);
return v_b_3007_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = l_Subarray_get___redArg(v_fst_3005_, v_a_3006_);
lean_inc(v_a_3006_);
v___x_3010_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3007_, v_a_3006_, v___x_3009_);
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_nat_add(v_a_3006_, v___x_3011_);
lean_dec(v_a_3006_);
v_a_3006_ = v___x_3012_;
v_b_3007_ = v___x_3010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3014_, lean_object* v_fst_3015_, lean_object* v___x_3016_, lean_object* v_fst_3017_, lean_object* v_a_3018_, lean_object* v_b_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3014_, v_fst_3015_, v___x_3016_, v_fst_3017_, v_a_3018_, v_b_3019_);
lean_dec_ref(v_fst_3017_);
lean_dec(v___x_3016_);
lean_dec_ref(v_fst_3015_);
lean_dec(v_upperBound_3014_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
if (lean_obj_tag(v_x_3022_) == 0)
{
lean_inc(v_x_3021_);
return v_x_3021_;
}
else
{
lean_object* v_key_3023_; lean_object* v_value_3024_; lean_object* v_tail_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_key_3023_ = lean_ctor_get(v_x_3022_, 0);
v_value_3024_ = lean_ctor_get(v_x_3022_, 1);
v_tail_3025_ = lean_ctor_get(v_x_3022_, 2);
v___x_3026_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3021_, v_tail_3025_);
lean_inc(v_value_3024_);
lean_inc(v_key_3023_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_key_3023_);
lean_ctor_set(v___x_3027_, 1, v_value_3024_);
v___x_3028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3026_);
return v___x_3028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3029_, v_x_3030_);
lean_dec(v_x_3030_);
lean_dec(v_x_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3032_, size_t v_i_3033_, size_t v_stop_3034_, lean_object* v_b_3035_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_eq(v_i_3033_, v_stop_3034_);
if (v___x_3036_ == 0)
{
size_t v___x_3037_; size_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_sub(v_i_3033_, v___x_3037_);
v___x_3039_ = lean_array_uget_borrowed(v_as_3032_, v___x_3038_);
v___x_3040_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3035_, v___x_3039_);
lean_dec(v_b_3035_);
v_i_3033_ = v___x_3038_;
v_b_3035_ = v___x_3040_;
goto _start;
}
else
{
return v_b_3035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3042_, lean_object* v_i_3043_, lean_object* v_stop_3044_, lean_object* v_b_3045_){
_start:
{
size_t v_i_boxed_3046_; size_t v_stop_boxed_3047_; lean_object* v_res_3048_; 
v_i_boxed_3046_ = lean_unbox_usize(v_i_3043_);
lean_dec(v_i_3043_);
v_stop_boxed_3047_ = lean_unbox_usize(v_stop_3044_);
lean_dec(v_stop_3044_);
v_res_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3042_, v_i_boxed_3046_, v_stop_boxed_3047_, v_b_3045_);
lean_dec_ref(v_as_3042_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3049_, lean_object* v_right_3050_, lean_object* v_pref_3051_){
_start:
{
lean_object* v_start_3052_; lean_object* v_stop_3053_; lean_object* v_i_3054_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_start_3052_ = lean_ctor_get(v_left_3049_, 1);
v_stop_3053_ = lean_ctor_get(v_left_3049_, 2);
v_i_3054_ = lean_array_get_size(v_pref_3051_);
v___x_3060_ = lean_nat_sub(v_stop_3053_, v_start_3052_);
v___x_3061_ = lean_nat_dec_lt(v_i_3054_, v___x_3060_);
lean_dec(v___x_3060_);
if (v___x_3061_ == 0)
{
goto v___jp_3055_;
}
else
{
lean_object* v_start_3062_; lean_object* v_stop_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_start_3062_ = lean_ctor_get(v_right_3050_, 1);
v_stop_3063_ = lean_ctor_get(v_right_3050_, 2);
v___x_3064_ = lean_nat_sub(v_stop_3063_, v_start_3062_);
v___x_3065_ = lean_nat_dec_lt(v_i_3054_, v___x_3064_);
lean_dec(v___x_3064_);
if (v___x_3065_ == 0)
{
goto v___jp_3055_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3066_ = l_Subarray_get___redArg(v_left_3049_, v_i_3054_);
v___x_3067_ = l_Subarray_get___redArg(v_right_3050_, v_i_3054_);
v___x_3068_ = lean_string_dec_eq(v___x_3066_, v___x_3067_);
lean_dec(v___x_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec(v___x_3066_);
v___x_3069_ = l_Subarray_drop___redArg(v_left_3049_, v_i_3054_);
v___x_3070_ = l_Subarray_drop___redArg(v_right_3050_, v_i_3054_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_pref_3051_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_array_push(v_pref_3051_, v___x_3066_);
v_pref_3051_ = v___x_3073_;
goto _start;
}
}
}
v___jp_3055_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3056_ = l_Subarray_drop___redArg(v_left_3049_, v_i_3054_);
v___x_3057_ = l_Subarray_drop___redArg(v_right_3050_, v_i_3054_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_pref_3051_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3077_, lean_object* v_right_3078_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3080_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3077_, v_right_3078_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3081_, lean_object* v_b_3082_){
_start:
{
lean_object* v_array_3083_; lean_object* v_start_3084_; lean_object* v_stop_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3098_; 
v_array_3083_ = lean_ctor_get(v_a_3081_, 0);
v_start_3084_ = lean_ctor_get(v_a_3081_, 1);
v_stop_3085_ = lean_ctor_get(v_a_3081_, 2);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_a_3081_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3087_ = v_a_3081_;
v_isShared_3088_ = v_isSharedCheck_3098_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_stop_3085_);
lean_inc(v_start_3084_);
lean_inc(v_array_3083_);
lean_dec(v_a_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3098_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_nat_dec_lt(v_start_3084_, v_stop_3085_);
if (v___x_3089_ == 0)
{
lean_del_object(v___x_3087_);
lean_dec(v_stop_3085_);
lean_dec(v_start_3084_);
lean_dec_ref(v_array_3083_);
return v_b_3082_;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3090_ = lean_unsigned_to_nat(1u);
v___x_3091_ = lean_nat_add(v_start_3084_, v___x_3090_);
lean_inc_ref(v_array_3083_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v___x_3091_);
v___x_3093_ = v___x_3087_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_array_3083_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_stop_3085_);
v___x_3093_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_array_fget(v_array_3083_, v_start_3084_);
lean_dec(v_start_3084_);
lean_dec_ref(v_array_3083_);
v___x_3095_ = lean_array_push(v_b_3082_, v___x_3094_);
v_a_3081_ = v___x_3093_;
v_b_3082_ = v___x_3095_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3099_, lean_object* v_right_3100_, lean_object* v_i_3101_){
_start:
{
lean_object* v_start_3102_; lean_object* v_stop_3103_; lean_object* v___x_3104_; uint8_t v___x_3118_; 
v_start_3102_ = lean_ctor_get(v_left_3099_, 1);
v_stop_3103_ = lean_ctor_get(v_left_3099_, 2);
v___x_3104_ = lean_nat_sub(v_stop_3103_, v_start_3102_);
v___x_3118_ = lean_nat_dec_lt(v_i_3101_, v___x_3104_);
if (v___x_3118_ == 0)
{
goto v___jp_3105_;
}
else
{
lean_object* v_start_3119_; lean_object* v_stop_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v_start_3119_ = lean_ctor_get(v_right_3100_, 1);
v_stop_3120_ = lean_ctor_get(v_right_3100_, 2);
v___x_3121_ = lean_nat_sub(v_stop_3120_, v_start_3119_);
v___x_3122_ = lean_nat_dec_lt(v_i_3101_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_dec(v___x_3121_);
goto v___jp_3105_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3123_ = lean_nat_sub(v___x_3104_, v_i_3101_);
lean_dec(v___x_3104_);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_sub(v___x_3123_, v___x_3124_);
v___x_3126_ = l_Subarray_get___redArg(v_left_3099_, v___x_3125_);
lean_dec(v___x_3125_);
v___x_3127_ = lean_nat_sub(v___x_3121_, v_i_3101_);
lean_dec(v___x_3121_);
v___x_3128_ = lean_nat_sub(v___x_3127_, v___x_3124_);
v___x_3129_ = l_Subarray_get___redArg(v_right_3100_, v___x_3128_);
lean_dec(v___x_3128_);
v___x_3130_ = lean_string_dec_eq(v___x_3126_, v___x_3129_);
lean_dec(v___x_3129_);
lean_dec(v___x_3126_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_i_3101_);
lean_inc_ref(v_left_3099_);
v___x_3131_ = l_Subarray_take___redArg(v_left_3099_, v___x_3123_);
v___x_3132_ = l_Subarray_take___redArg(v_right_3100_, v___x_3127_);
lean_dec(v___x_3127_);
v___x_3133_ = l_Subarray_drop___redArg(v_left_3099_, v___x_3123_);
lean_dec(v___x_3123_);
v___x_3134_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3135_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3133_, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3132_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3131_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
return v___x_3137_;
}
else
{
lean_object* v___x_3138_; 
lean_dec(v___x_3127_);
lean_dec(v___x_3123_);
v___x_3138_ = lean_nat_add(v_i_3101_, v___x_3124_);
lean_dec(v_i_3101_);
v_i_3101_ = v___x_3138_;
goto _start;
}
}
}
v___jp_3105_:
{
lean_object* v_start_3106_; lean_object* v_stop_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_start_3106_ = lean_ctor_get(v_right_3100_, 1);
v_stop_3107_ = lean_ctor_get(v_right_3100_, 2);
v___x_3108_ = lean_nat_sub(v___x_3104_, v_i_3101_);
lean_dec(v___x_3104_);
lean_inc_ref(v_left_3099_);
v___x_3109_ = l_Subarray_take___redArg(v_left_3099_, v___x_3108_);
v___x_3110_ = lean_nat_sub(v_stop_3107_, v_start_3106_);
v___x_3111_ = lean_nat_sub(v___x_3110_, v_i_3101_);
lean_dec(v_i_3101_);
lean_dec(v___x_3110_);
v___x_3112_ = l_Subarray_take___redArg(v_right_3100_, v___x_3111_);
lean_dec(v___x_3111_);
v___x_3113_ = l_Subarray_drop___redArg(v_left_3099_, v___x_3108_);
lean_dec(v___x_3108_);
v___x_3114_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3115_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3113_, v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3112_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3109_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3140_, lean_object* v_right_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3140_, v_right_3141_, v___x_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3144_, lean_object* v_b_3145_){
_start:
{
if (lean_obj_tag(v_as_x27_3144_) == 0)
{
return v_b_3145_;
}
else
{
lean_object* v_head_3146_; lean_object* v_snd_3147_; lean_object* v_leftIndex_3148_; 
v_head_3146_ = lean_ctor_get(v_as_x27_3144_, 0);
lean_inc(v_head_3146_);
v_snd_3147_ = lean_ctor_get(v_head_3146_, 1);
lean_inc(v_snd_3147_);
v_leftIndex_3148_ = lean_ctor_get(v_snd_3147_, 1);
lean_inc(v_leftIndex_3148_);
if (lean_obj_tag(v_leftIndex_3148_) == 1)
{
lean_object* v_rightIndex_3149_; 
v_rightIndex_3149_ = lean_ctor_get(v_snd_3147_, 3);
lean_inc(v_rightIndex_3149_);
if (lean_obj_tag(v_rightIndex_3149_) == 1)
{
if (lean_obj_tag(v_b_3145_) == 0)
{
lean_object* v_tail_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3180_; 
v_tail_3150_ = lean_ctor_get(v_as_x27_3144_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_as_x27_3144_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v_as_x27_3144_, 0);
lean_dec(v_unused_3181_);
v___x_3152_ = v_as_x27_3144_;
v_isShared_3153_ = v_isSharedCheck_3180_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_tail_3150_);
lean_dec(v_as_x27_3144_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3180_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_fst_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3178_; 
v_fst_3154_ = lean_ctor_get(v_head_3146_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_head_3146_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v_head_3146_, 1);
lean_dec(v_unused_3179_);
v___x_3156_ = v_head_3146_;
v_isShared_3157_ = v_isSharedCheck_3178_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_fst_3154_);
lean_dec(v_head_3146_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3178_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_leftCount_3158_; lean_object* v_rightCount_3159_; lean_object* v_val_3160_; lean_object* v_val_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3177_; 
v_leftCount_3158_ = lean_ctor_get(v_snd_3147_, 0);
lean_inc(v_leftCount_3158_);
v_rightCount_3159_ = lean_ctor_get(v_snd_3147_, 2);
lean_inc(v_rightCount_3159_);
lean_dec(v_snd_3147_);
v_val_3160_ = lean_ctor_get(v_leftIndex_3148_, 0);
lean_inc(v_val_3160_);
lean_dec_ref(v_leftIndex_3148_);
v_val_3161_ = lean_ctor_get(v_rightIndex_3149_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_rightIndex_3149_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3163_ = v_rightIndex_3149_;
v_isShared_3164_ = v_isSharedCheck_3177_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_val_3161_);
lean_dec(v_rightIndex_3149_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3177_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_nat_add(v_leftCount_3158_, v_rightCount_3159_);
lean_dec(v_rightCount_3159_);
lean_dec(v_leftCount_3158_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v_val_3161_);
lean_ctor_set(v___x_3156_, 0, v_val_3160_);
v___x_3167_ = v___x_3156_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_val_3160_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_val_3161_);
v___x_3167_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 0);
lean_ctor_set(v___x_3152_, 1, v___x_3167_);
lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
v___x_3169_ = v___x_3152_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_fst_3154_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3165_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3170_);
v___x_3172_ = v___x_3163_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
v_as_x27_3144_ = v_tail_3150_;
v_b_3145_ = v___x_3172_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_val_3182_; lean_object* v_tail_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3224_; 
v_val_3182_ = lean_ctor_get(v_b_3145_, 0);
lean_inc(v_val_3182_);
v_tail_3183_ = lean_ctor_get(v_as_x27_3144_, 1);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_as_x27_3144_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; 
v_unused_3225_ = lean_ctor_get(v_as_x27_3144_, 0);
lean_dec(v_unused_3225_);
v___x_3185_ = v_as_x27_3144_;
v_isShared_3186_ = v_isSharedCheck_3224_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_tail_3183_);
lean_dec(v_as_x27_3144_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3224_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_fst_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3222_; 
v_fst_3187_ = lean_ctor_get(v_head_3146_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_head_3146_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; 
v_unused_3223_ = lean_ctor_get(v_head_3146_, 1);
lean_dec(v_unused_3223_);
v___x_3189_ = v_head_3146_;
v_isShared_3190_ = v_isSharedCheck_3222_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_fst_3187_);
lean_dec(v_head_3146_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3222_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_leftCount_3191_; lean_object* v_rightCount_3192_; lean_object* v_val_3193_; lean_object* v_val_3194_; lean_object* v_fst_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3220_; 
v_leftCount_3191_ = lean_ctor_get(v_snd_3147_, 0);
lean_inc(v_leftCount_3191_);
v_rightCount_3192_ = lean_ctor_get(v_snd_3147_, 2);
lean_inc(v_rightCount_3192_);
lean_dec(v_snd_3147_);
v_val_3193_ = lean_ctor_get(v_leftIndex_3148_, 0);
lean_inc(v_val_3193_);
lean_dec_ref(v_leftIndex_3148_);
v_val_3194_ = lean_ctor_get(v_rightIndex_3149_, 0);
lean_inc(v_val_3194_);
lean_dec_ref(v_rightIndex_3149_);
v_fst_3195_ = lean_ctor_get(v_val_3182_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_val_3182_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_val_3182_, 1);
lean_dec(v_unused_3221_);
v___x_3197_ = v_val_3182_;
v_isShared_3198_ = v_isSharedCheck_3220_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_fst_3195_);
lean_dec(v_val_3182_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3220_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = lean_nat_add(v_leftCount_3191_, v_rightCount_3192_);
lean_dec(v_rightCount_3192_);
lean_dec(v_leftCount_3191_);
v___x_3200_ = lean_nat_dec_lt(v___x_3199_, v_fst_3195_);
lean_dec(v_fst_3195_);
if (v___x_3200_ == 0)
{
lean_dec(v___x_3199_);
lean_del_object(v___x_3197_);
lean_dec(v_val_3194_);
lean_dec(v_val_3193_);
lean_del_object(v___x_3189_);
lean_dec(v_fst_3187_);
lean_del_object(v___x_3185_);
v_as_x27_3144_ = v_tail_3183_;
goto _start;
}
else
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3218_; 
v_isSharedCheck_3218_ = !lean_is_exclusive(v_b_3145_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; 
v_unused_3219_ = lean_ctor_get(v_b_3145_, 0);
lean_dec(v_unused_3219_);
v___x_3203_ = v_b_3145_;
v_isShared_3204_ = v_isSharedCheck_3218_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v_b_3145_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3218_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v_val_3194_);
lean_ctor_set(v___x_3197_, 0, v_val_3193_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_val_3193_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_val_3194_);
v___x_3206_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 1, v___x_3206_);
v___x_3208_ = v___x_3189_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_fst_3187_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3210_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 0);
lean_ctor_set(v___x_3185_, 1, v___x_3208_);
lean_ctor_set(v___x_3185_, 0, v___x_3199_);
v___x_3210_ = v___x_3185_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3212_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3210_);
v___x_3212_ = v___x_3203_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
v_as_x27_3144_ = v_tail_3183_;
v_b_3145_ = v___x_3212_;
goto _start;
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
}
else
{
lean_object* v_tail_3226_; 
lean_dec_ref(v_leftIndex_3148_);
lean_dec(v_rightIndex_3149_);
lean_dec(v_snd_3147_);
lean_dec(v_head_3146_);
v_tail_3226_ = lean_ctor_get(v_as_x27_3144_, 1);
lean_inc(v_tail_3226_);
lean_dec_ref(v_as_x27_3144_);
v_as_x27_3144_ = v_tail_3226_;
goto _start;
}
}
else
{
lean_object* v_tail_3228_; 
lean_dec(v_leftIndex_3148_);
lean_dec(v_snd_3147_);
lean_dec(v_head_3146_);
v_tail_3228_ = lean_ctor_get(v_as_x27_3144_, 1);
lean_inc(v_tail_3228_);
lean_dec_ref(v_as_x27_3144_);
v_as_x27_3144_ = v_tail_3228_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3230_, lean_object* v_index_3231_, lean_object* v_val_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3230_, v_val_3232_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_index_3231_);
v___x_3238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3234_);
lean_ctor_set(v___x_3238_, 1, v___x_3235_);
lean_ctor_set(v___x_3238_, 2, v___x_3236_);
lean_ctor_set(v___x_3238_, 3, v___x_3237_);
v___x_3239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3230_, v_val_3232_, v___x_3238_);
return v___x_3239_;
}
else
{
lean_object* v_val_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3261_; 
v_val_3240_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3242_ = v___x_3233_;
v_isShared_3243_ = v_isSharedCheck_3261_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_val_3240_);
lean_dec(v___x_3233_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3261_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_leftCount_3244_; lean_object* v_leftIndex_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3258_; 
v_leftCount_3244_ = lean_ctor_get(v_val_3240_, 0);
v_leftIndex_3245_ = lean_ctor_get(v_val_3240_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_val_3240_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; lean_object* v_unused_3260_; 
v_unused_3259_ = lean_ctor_get(v_val_3240_, 3);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_val_3240_, 2);
lean_dec(v_unused_3260_);
v___x_3247_ = v_val_3240_;
v_isShared_3248_ = v_isSharedCheck_3258_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_leftIndex_3245_);
lean_inc(v_leftCount_3244_);
lean_dec(v_val_3240_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3258_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_nat_add(v_leftCount_3244_, v___x_3249_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v_index_3231_);
v___x_3252_ = v___x_3242_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_index_3231_);
v___x_3252_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 3, v___x_3252_);
lean_ctor_set(v___x_3247_, 2, v___x_3250_);
v___x_3254_ = v___x_3247_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_leftCount_3244_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_leftIndex_3245_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3230_, v_val_3232_, v___x_3254_);
return v___x_3255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3262_, lean_object* v___x_3263_, lean_object* v_fst_3264_, lean_object* v___x_3265_, lean_object* v_a_3266_, lean_object* v_b_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = lean_nat_dec_lt(v_a_3266_, v_upperBound_3262_);
if (v___x_3268_ == 0)
{
lean_dec(v_a_3266_);
return v_b_3267_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3269_ = l_Subarray_get___redArg(v_fst_3264_, v_a_3266_);
lean_inc(v_a_3266_);
v___x_3270_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3267_, v_a_3266_, v___x_3269_);
v___x_3271_ = lean_unsigned_to_nat(1u);
v___x_3272_ = lean_nat_add(v_a_3266_, v___x_3271_);
lean_dec(v_a_3266_);
v_a_3266_ = v___x_3272_;
v_b_3267_ = v___x_3270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3274_, lean_object* v___x_3275_, lean_object* v_fst_3276_, lean_object* v___x_3277_, lean_object* v_a_3278_, lean_object* v_b_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3274_, v___x_3275_, v_fst_3276_, v___x_3277_, v_a_3278_, v_b_3279_);
lean_dec(v___x_3277_);
lean_dec_ref(v_fst_3276_);
lean_dec(v___x_3275_);
lean_dec(v_upperBound_3274_);
return v_res_3280_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_unsigned_to_nat(16u);
v___x_3283_ = lean_mk_array(v___x_3282_, v___x_3281_);
return v___x_3283_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_hist_3286_; 
v___x_3284_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3285_ = lean_unsigned_to_nat(0u);
v_hist_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3286_, 0, v___x_3285_);
lean_ctor_set(v_hist_3286_, 1, v___x_3284_);
return v_hist_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3287_, lean_object* v_right_3288_){
_start:
{
lean_object* v___x_3289_; lean_object* v_snd_3290_; lean_object* v_fst_3291_; lean_object* v_fst_3292_; lean_object* v_snd_3293_; lean_object* v___x_3294_; lean_object* v_snd_3295_; lean_object* v_fst_3296_; lean_object* v_fst_3297_; lean_object* v_snd_3298_; lean_object* v_start_3299_; lean_object* v_stop_3300_; lean_object* v___x_3301_; lean_object* v_hist_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v_start_3305_; lean_object* v_stop_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_buckets_3309_; lean_object* v___x_3310_; lean_object* v___y_3312_; lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3289_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3287_, v_right_3288_);
v_snd_3290_ = lean_ctor_get(v___x_3289_, 1);
lean_inc(v_snd_3290_);
v_fst_3291_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_fst_3291_);
lean_dec_ref(v___x_3289_);
v_fst_3292_ = lean_ctor_get(v_snd_3290_, 0);
lean_inc(v_fst_3292_);
v_snd_3293_ = lean_ctor_get(v_snd_3290_, 1);
lean_inc(v_snd_3293_);
lean_dec(v_snd_3290_);
v___x_3294_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3292_, v_snd_3293_);
v_snd_3295_ = lean_ctor_get(v___x_3294_, 1);
lean_inc(v_snd_3295_);
v_fst_3296_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_fst_3296_);
lean_dec_ref(v___x_3294_);
v_fst_3297_ = lean_ctor_get(v_snd_3295_, 0);
lean_inc(v_fst_3297_);
v_snd_3298_ = lean_ctor_get(v_snd_3295_, 1);
lean_inc(v_snd_3298_);
lean_dec(v_snd_3295_);
v_start_3299_ = lean_ctor_get(v_fst_3296_, 1);
v_stop_3300_ = lean_ctor_get(v_fst_3296_, 2);
v___x_3301_ = lean_unsigned_to_nat(0u);
v_hist_3302_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3303_ = lean_nat_sub(v_stop_3300_, v_start_3299_);
v___x_3304_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3303_, v_fst_3297_, v___x_3303_, v_fst_3296_, v___x_3301_, v_hist_3302_);
v_start_3305_ = lean_ctor_get(v_fst_3297_, 1);
v_stop_3306_ = lean_ctor_get(v_fst_3297_, 2);
v___x_3307_ = lean_nat_sub(v_stop_3306_, v_start_3305_);
v___x_3308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3307_, v___x_3307_, v_fst_3297_, v___x_3303_, v___x_3301_, v___x_3304_);
lean_dec(v___x_3303_);
lean_dec(v___x_3307_);
v_buckets_3309_ = lean_ctor_get(v___x_3308_, 1);
lean_inc_ref(v_buckets_3309_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = lean_box(0);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_array_get_size(v_buckets_3309_);
v___x_3340_ = lean_nat_dec_lt(v___x_3301_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_dec_ref(v_buckets_3309_);
v___y_3312_ = v___x_3338_;
goto v___jp_3311_;
}
else
{
size_t v___x_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_usize_of_nat(v___x_3339_);
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3309_, v___x_3341_, v___x_3342_, v___x_3338_);
lean_dec_ref(v_buckets_3309_);
v___y_3312_ = v___x_3343_;
goto v___jp_3311_;
}
v___jp_3311_:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3312_, v___x_3310_);
if (lean_obj_tag(v___x_3313_) == 1)
{
lean_object* v_val_3314_; lean_object* v_snd_3315_; lean_object* v_snd_3316_; lean_object* v_fst_3317_; lean_object* v_fst_3318_; lean_object* v_snd_3319_; lean_object* v___x_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3323_; lean_object* v_fst_3324_; lean_object* v_snd_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_val_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_val_3314_);
lean_dec_ref(v___x_3313_);
v_snd_3315_ = lean_ctor_get(v_val_3314_, 1);
lean_inc(v_snd_3315_);
lean_dec(v_val_3314_);
v_snd_3316_ = lean_ctor_get(v_snd_3315_, 1);
lean_inc(v_snd_3316_);
v_fst_3317_ = lean_ctor_get(v_snd_3315_, 0);
lean_inc(v_fst_3317_);
lean_dec(v_snd_3315_);
v_fst_3318_ = lean_ctor_get(v_snd_3316_, 0);
lean_inc(v_fst_3318_);
v_snd_3319_ = lean_ctor_get(v_snd_3316_, 1);
lean_inc(v_snd_3319_);
lean_dec(v_snd_3316_);
v___x_3320_ = l_Subarray_split___redArg(v_fst_3296_, v_fst_3318_);
lean_dec(v_fst_3318_);
v_fst_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_fst_3321_);
v_snd_3322_ = lean_ctor_get(v___x_3320_, 1);
lean_inc(v_snd_3322_);
lean_dec_ref(v___x_3320_);
v___x_3323_ = l_Subarray_split___redArg(v_fst_3297_, v_snd_3319_);
lean_dec(v_snd_3319_);
v_fst_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_fst_3324_);
v_snd_3325_ = lean_ctor_get(v___x_3323_, 1);
lean_inc(v_snd_3325_);
lean_dec_ref(v___x_3323_);
v___x_3326_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3321_, v_fst_3324_);
v___x_3327_ = l_Array_append___redArg(v_fst_3291_, v___x_3326_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(1u);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3328_);
v___x_3330_ = lean_array_push(v___x_3329_, v_fst_3317_);
v___x_3331_ = l_Array_append___redArg(v___x_3327_, v___x_3330_);
lean_dec_ref(v___x_3330_);
v___x_3332_ = l_Subarray_drop___redArg(v_snd_3322_, v___x_3328_);
v___x_3333_ = l_Subarray_drop___redArg(v_snd_3325_, v___x_3328_);
v___x_3334_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3332_, v___x_3333_);
v___x_3335_ = l_Array_append___redArg(v___x_3331_, v___x_3334_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = l_Array_append___redArg(v___x_3335_, v_snd_3298_);
lean_dec(v_snd_3298_);
return v___x_3336_;
}
else
{
lean_object* v___x_3337_; 
lean_dec(v___x_3313_);
lean_dec(v_fst_3297_);
lean_dec(v_fst_3296_);
v___x_3337_ = l_Array_append___redArg(v_fst_3291_, v_snd_3298_);
lean_dec(v_snd_3298_);
return v___x_3337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3344_, lean_object* v_original_3345_, lean_object* v_b_3346_){
_start:
{
lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3367_; 
v_fst_3347_ = lean_ctor_get(v_b_3346_, 0);
v_snd_3348_ = lean_ctor_get(v_b_3346_, 1);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_b_3346_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3350_ = v_b_3346_;
v_isShared_3351_ = v_isSharedCheck_3367_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_snd_3348_);
lean_inc(v_fst_3347_);
lean_dec(v_b_3346_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3367_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
uint8_t v___x_3352_; 
v___x_3352_ = lean_nat_dec_lt(v_snd_3348_, v___x_3344_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3354_; 
if (v_isShared_3351_ == 0)
{
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_fst_3347_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_snd_3348_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
else
{
uint8_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3356_ = 1;
v___x_3357_ = lean_array_fget_borrowed(v_original_3345_, v_snd_3348_);
v___x_3358_ = lean_box(v___x_3356_);
lean_inc(v___x_3357_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 1, v___x_3357_);
lean_ctor_set(v___x_3350_, 0, v___x_3358_);
v___x_3360_ = v___x_3350_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3357_);
v___x_3360_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3361_ = lean_array_push(v_fst_3347_, v___x_3360_);
v___x_3362_ = lean_unsigned_to_nat(1u);
v___x_3363_ = lean_nat_add(v_snd_3348_, v___x_3362_);
lean_dec(v_snd_3348_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3361_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v_b_3346_ = v___x_3364_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3368_, lean_object* v_original_3369_, lean_object* v_b_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3368_, v_original_3369_, v_b_3370_);
lean_dec_ref(v_original_3369_);
lean_dec(v___x_3368_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3372_, size_t v_i_3373_, lean_object* v_bs_3374_){
_start:
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_usize_dec_lt(v_i_3373_, v_sz_3372_);
if (v___x_3375_ == 0)
{
return v_bs_3374_;
}
else
{
lean_object* v_v_3376_; lean_object* v___x_3377_; lean_object* v_bs_x27_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; size_t v___x_3382_; size_t v___x_3383_; lean_object* v___x_3384_; 
v_v_3376_ = lean_array_uget(v_bs_3374_, v_i_3373_);
v___x_3377_ = lean_unsigned_to_nat(0u);
v_bs_x27_3378_ = lean_array_uset(v_bs_3374_, v_i_3373_, v___x_3377_);
v___x_3379_ = 0;
v___x_3380_ = lean_box(v___x_3379_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v_v_3376_);
v___x_3382_ = ((size_t)1ULL);
v___x_3383_ = lean_usize_add(v_i_3373_, v___x_3382_);
v___x_3384_ = lean_array_uset(v_bs_x27_3378_, v_i_3373_, v___x_3381_);
v_i_3373_ = v___x_3383_;
v_bs_3374_ = v___x_3384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3386_, lean_object* v_i_3387_, lean_object* v_bs_3388_){
_start:
{
size_t v_sz_boxed_3389_; size_t v_i_boxed_3390_; lean_object* v_res_3391_; 
v_sz_boxed_3389_ = lean_unbox_usize(v_sz_3386_);
lean_dec(v_sz_3386_);
v_i_boxed_3390_ = lean_unbox_usize(v_i_3387_);
lean_dec(v_i_3387_);
v_res_3391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3389_, v_i_boxed_3390_, v_bs_3388_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3392_, size_t v_i_3393_, lean_object* v_bs_3394_){
_start:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_usize_dec_lt(v_i_3393_, v_sz_3392_);
if (v___x_3395_ == 0)
{
return v_bs_3394_;
}
else
{
lean_object* v_v_3396_; lean_object* v___x_3397_; lean_object* v_bs_x27_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; size_t v___x_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v_v_3396_ = lean_array_uget(v_bs_3394_, v_i_3393_);
v___x_3397_ = lean_unsigned_to_nat(0u);
v_bs_x27_3398_ = lean_array_uset(v_bs_3394_, v_i_3393_, v___x_3397_);
v___x_3399_ = 1;
v___x_3400_ = lean_box(v___x_3399_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v_v_3396_);
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3393_, v___x_3402_);
v___x_3404_ = lean_array_uset(v_bs_x27_3398_, v_i_3393_, v___x_3401_);
v_i_3393_ = v___x_3403_;
v_bs_3394_ = v___x_3404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3406_, lean_object* v_i_3407_, lean_object* v_bs_3408_){
_start:
{
size_t v_sz_boxed_3409_; size_t v_i_boxed_3410_; lean_object* v_res_3411_; 
v_sz_boxed_3409_ = lean_unbox_usize(v_sz_3406_);
lean_dec(v_sz_3406_);
v_i_boxed_3410_ = lean_unbox_usize(v_i_3407_);
lean_dec(v_i_3407_);
v_res_3411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3409_, v_i_boxed_3410_, v_bs_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_inst_3419_, lean_object* v_original_3420_, lean_object* v_edited_3421_){
_start:
{
lean_object* v_i_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v_i_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_array_get_size(v_original_3420_);
v___x_3424_ = lean_nat_dec_lt(v_i_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
size_t v_sz_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
lean_dec_ref(v_original_3420_);
lean_dec_ref(v_inst_3419_);
v_sz_3425_ = lean_array_size(v_edited_3421_);
v___x_3426_ = ((size_t)0ULL);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3425_, v___x_3426_, v_edited_3421_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = lean_array_get_size(v_edited_3421_);
v___x_3429_ = lean_nat_dec_lt(v_i_3422_, v___x_3428_);
if (v___x_3429_ == 0)
{
size_t v_sz_3430_; size_t v___x_3431_; lean_object* v___x_3432_; 
lean_dec_ref(v_edited_3421_);
lean_dec_ref(v_inst_3419_);
v_sz_3430_ = lean_array_size(v_original_3420_);
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3430_, v___x_3431_, v_original_3420_);
return v___x_3432_;
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v_ds_3435_; lean_object* v___x_3436_; size_t v_sz_3437_; size_t v___x_3438_; lean_object* v___x_3439_; lean_object* v_snd_3440_; lean_object* v_fst_3441_; lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3462_; 
lean_inc_ref(v_original_3420_);
v___x_3433_ = l_Array_toSubarray___redArg(v_original_3420_, v_i_3422_, v___x_3423_);
lean_inc_ref(v_edited_3421_);
v___x_3434_ = l_Array_toSubarray___redArg(v_edited_3421_, v_i_3422_, v___x_3428_);
v_ds_3435_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3433_, v___x_3434_);
v___x_3436_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3437_ = lean_array_size(v_ds_3435_);
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_inst_3419_, v_edited_3421_, v___x_3428_, v_original_3420_, v___x_3423_, v_ds_3435_, v_sz_3437_, v___x_3438_, v___x_3436_);
lean_dec_ref(v_ds_3435_);
v_snd_3440_ = lean_ctor_get(v___x_3439_, 1);
lean_inc(v_snd_3440_);
v_fst_3441_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_fst_3441_);
lean_dec_ref(v___x_3439_);
v_fst_3442_ = lean_ctor_get(v_snd_3440_, 0);
v_snd_3443_ = lean_ctor_get(v_snd_3440_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_snd_3440_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3445_ = v_snd_3440_;
v_isShared_3446_ = v_isSharedCheck_3462_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_inc(v_fst_3442_);
lean_dec(v_snd_3440_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3462_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v_fst_3442_);
lean_ctor_set(v___x_3445_, 0, v_fst_3441_);
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3441_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_fst_3442_);
v___x_3448_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; lean_object* v_fst_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3459_; 
v___x_3449_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3423_, v_original_3420_, v___x_3448_);
lean_dec_ref(v_original_3420_);
v_fst_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v___x_3449_, 1);
lean_dec(v_unused_3460_);
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3459_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_fst_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3459_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v_snd_3443_);
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3450_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3443_);
v___x_3455_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v_fst_3457_; 
v___x_3456_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3428_, v_edited_3421_, v___x_3455_);
lean_dec_ref(v_edited_3421_);
v_fst_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_fst_3457_);
lean_dec_ref(v___x_3456_);
return v_fst_3457_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3463_, lean_object* v_x_3464_, lean_object* v_x_3465_){
_start:
{
if (lean_obj_tag(v_x_3464_) == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = l_List_reverse___redArg(v_x_3465_);
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
return v___x_3468_;
}
else
{
lean_object* v_head_3469_; lean_object* v_tail_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3479_; 
v_head_3469_ = lean_ctor_get(v_x_3464_, 0);
v_tail_3470_ = lean_ctor_get(v_x_3464_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_x_3464_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3472_ = v_x_3464_;
v_isShared_3473_ = v_isSharedCheck_3479_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_tail_3470_);
lean_inc(v_head_3469_);
lean_dec(v_x_3464_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3479_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3474_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3469_, v___y_3463_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v_x_3465_);
lean_ctor_set(v___x_3472_, 0, v___x_3474_);
v___x_3476_ = v___x_3472_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_x_3465_);
v___x_3476_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
v_x_3464_ = v_tail_3470_;
v_x_3465_ = v___x_3476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3480_, lean_object* v_x_3481_, lean_object* v_x_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3480_, v_x_3481_, v_x_3482_);
lean_dec(v___y_3480_);
return v_res_3484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = l_Lean_MessageLog_empty;
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; uint8_t v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v_dc_x3f_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3750_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3501_);
v___x_3751_ = l_Lean_Syntax_isOfKind(v_x_3501_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
lean_dec(v_x_3501_);
v___x_3752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3752_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = l_Lean_Syntax_getArg(v_x_3501_, v___x_3753_);
v___x_3755_ = l_Lean_Syntax_isNone(v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3754_);
v___x_3757_ = l_Lean_Syntax_matchesNull(v___x_3754_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
lean_dec(v___x_3754_);
lean_dec(v_x_3501_);
v___x_3758_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3758_;
}
else
{
lean_object* v_dc_x3f_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v_dc_x3f_3759_ = l_Lean_Syntax_getArg(v___x_3754_, v___x_3753_);
lean_dec(v___x_3754_);
v___x_3760_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3759_);
v___x_3761_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3759_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; 
lean_dec(v_dc_x3f_3759_);
lean_dec(v_x_3501_);
v___x_3762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_dc_x3f_3759_);
v_dc_x3f_3731_ = v___x_3763_;
v___y_3732_ = v_a_3502_;
v___y_3733_ = v_a_3503_;
goto v___jp_3730_;
}
}
}
else
{
lean_object* v___x_3764_; 
lean_dec(v___x_3754_);
v___x_3764_ = lean_box(0);
v_dc_x3f_3731_ = v___x_3764_;
v___y_3732_ = v_a_3502_;
v___y_3733_ = v_a_3503_;
goto v___jp_3730_;
}
}
v___jp_3505_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3511_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3512_ = l_Lean_stringToMessageData(v___y_3510_);
v___x_3513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3511_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3506_, v___x_3513_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3506_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3535_; 
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v___x_3514_, 0);
lean_dec(v_unused_3536_);
v___x_3516_ = v___x_3514_;
v_isShared_3517_ = v_isSharedCheck_3535_;
goto v_resetjp_3515_;
}
else
{
lean_dec(v___x_3514_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3535_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Elab_Command_getRef___redArg(v___y_3507_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___y_3509_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_a_3519_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 10);
lean_ctor_set(v___x_3516_, 0, v___x_3522_);
v___x_3524_ = v___x_3516_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3524_, v___y_3507_, v___y_3508_);
lean_dec_ref(v___y_3507_);
return v___x_3525_;
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_del_object(v___x_3516_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3507_);
v_a_3527_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3518_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3518_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3507_);
return v___x_3514_;
}
}
v___jp_3537_:
{
if (v___y_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v_env_3548_; lean_object* v_scopes_3549_; lean_object* v_usedQuotCtxts_3550_; lean_object* v_nextMacroScope_3551_; lean_object* v_maxRecDepth_3552_; lean_object* v_ngen_3553_; lean_object* v_auxDeclNGen_3554_; lean_object* v_infoState_3555_; lean_object* v_traceState_3556_; lean_object* v_snapshotTasks_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v___y_3538_);
v___x_3547_ = lean_st_ref_take(v___y_3543_);
v_env_3548_ = lean_ctor_get(v___x_3547_, 0);
v_scopes_3549_ = lean_ctor_get(v___x_3547_, 2);
v_usedQuotCtxts_3550_ = lean_ctor_get(v___x_3547_, 3);
v_nextMacroScope_3551_ = lean_ctor_get(v___x_3547_, 4);
v_maxRecDepth_3552_ = lean_ctor_get(v___x_3547_, 5);
v_ngen_3553_ = lean_ctor_get(v___x_3547_, 6);
v_auxDeclNGen_3554_ = lean_ctor_get(v___x_3547_, 7);
v_infoState_3555_ = lean_ctor_get(v___x_3547_, 8);
v_traceState_3556_ = lean_ctor_get(v___x_3547_, 9);
v_snapshotTasks_3557_ = lean_ctor_get(v___x_3547_, 10);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v___x_3547_, 1);
lean_dec(v_unused_3585_);
v___x_3559_ = v___x_3547_;
v_isShared_3560_ = v_isSharedCheck_3584_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snapshotTasks_3557_);
lean_inc(v_traceState_3556_);
lean_inc(v_infoState_3555_);
lean_inc(v_auxDeclNGen_3554_);
lean_inc(v_ngen_3553_);
lean_inc(v_maxRecDepth_3552_);
lean_inc(v_nextMacroScope_3551_);
lean_inc(v_usedQuotCtxts_3550_);
lean_inc(v_scopes_3549_);
lean_inc(v_env_3548_);
lean_dec(v___x_3547_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3584_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v___y_3542_);
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_env_3548_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___y_3542_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_scopes_3549_);
lean_ctor_set(v_reuseFailAlloc_3583_, 3, v_usedQuotCtxts_3550_);
lean_ctor_set(v_reuseFailAlloc_3583_, 4, v_nextMacroScope_3551_);
lean_ctor_set(v_reuseFailAlloc_3583_, 5, v_maxRecDepth_3552_);
lean_ctor_set(v_reuseFailAlloc_3583_, 6, v_ngen_3553_);
lean_ctor_set(v_reuseFailAlloc_3583_, 7, v_auxDeclNGen_3554_);
lean_ctor_set(v_reuseFailAlloc_3583_, 8, v_infoState_3555_);
lean_ctor_set(v_reuseFailAlloc_3583_, 9, v_traceState_3556_);
lean_ctor_set(v_reuseFailAlloc_3583_, 10, v_snapshotTasks_3557_);
v___x_3562_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_scopes_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v_opts_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3563_ = lean_st_ref_set(v___y_3543_, v___x_3562_);
v___x_3564_ = lean_st_ref_get(v___y_3543_);
v_scopes_3565_ = lean_ctor_get(v___x_3564_, 2);
lean_inc(v_scopes_3565_);
lean_dec(v___x_3564_);
v___x_3566_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3567_ = l_List_head_x21___redArg(v___x_3566_, v_scopes_3565_);
lean_dec(v_scopes_3565_);
v_opts_3568_ = lean_ctor_get(v___x_3567_, 1);
lean_inc_ref(v_opts_3568_);
lean_dec(v___x_3567_);
v___x_3569_ = l_guard__msgs_diff;
v___x_3570_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3568_, v___x_3569_);
lean_dec_ref(v_opts_3568_);
if (v___x_3570_ == 0)
{
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3540_);
lean_inc_ref(v___y_3545_);
v___y_3506_ = v___y_3539_;
v___y_3507_ = v___y_3541_;
v___y_3508_ = v___y_3543_;
v___y_3509_ = v___y_3545_;
v___y_3510_ = v___y_3545_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_3572_ = lean_string_utf8_byte_size(v___y_3544_);
lean_inc(v___y_3540_);
lean_inc_ref(v___y_3544_);
v___x_3573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3573_, 0, v___y_3544_);
lean_ctor_set(v___x_3573_, 1, v___y_3540_);
lean_ctor_set(v___x_3573_, 2, v___x_3572_);
v___x_3574_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3573_);
v___x_3575_ = lean_mk_empty_array_with_capacity(v___y_3540_);
lean_inc_ref(v___x_3575_);
v___x_3576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3544_, v___x_3573_, v___x_3572_, v___x_3574_, v___x_3575_);
lean_dec_ref(v___x_3573_);
v___x_3577_ = lean_string_utf8_byte_size(v___y_3545_);
lean_inc_ref(v___y_3545_);
v___x_3578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3578_, 0, v___y_3545_);
lean_ctor_set(v___x_3578_, 1, v___y_3540_);
lean_ctor_set(v___x_3578_, 2, v___x_3577_);
v___x_3579_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3578_);
lean_inc_ref(v___y_3545_);
v___x_3580_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3545_, v___x_3578_, v___x_3577_, v___x_3579_, v___x_3575_);
lean_dec_ref(v___x_3578_);
v___x_3581_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3571_, v___x_3576_, v___x_3580_);
v___x_3582_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3581_);
lean_dec_ref(v___x_3581_);
v___y_3506_ = v___y_3539_;
v___y_3507_ = v___y_3541_;
v___y_3508_ = v___y_3543_;
v___y_3509_ = v___y_3545_;
v___y_3510_ = v___x_3582_;
goto v___jp_3505_;
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v_env_3587_; lean_object* v_scopes_3588_; lean_object* v_usedQuotCtxts_3589_; lean_object* v_nextMacroScope_3590_; lean_object* v_maxRecDepth_3591_; lean_object* v_ngen_3592_; lean_object* v_auxDeclNGen_3593_; lean_object* v_infoState_3594_; lean_object* v_traceState_3595_; lean_object* v_snapshotTasks_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec(v___y_3539_);
v___x_3586_ = lean_st_ref_take(v___y_3543_);
v_env_3587_ = lean_ctor_get(v___x_3586_, 0);
v_scopes_3588_ = lean_ctor_get(v___x_3586_, 2);
v_usedQuotCtxts_3589_ = lean_ctor_get(v___x_3586_, 3);
v_nextMacroScope_3590_ = lean_ctor_get(v___x_3586_, 4);
v_maxRecDepth_3591_ = lean_ctor_get(v___x_3586_, 5);
v_ngen_3592_ = lean_ctor_get(v___x_3586_, 6);
v_auxDeclNGen_3593_ = lean_ctor_get(v___x_3586_, 7);
v_infoState_3594_ = lean_ctor_get(v___x_3586_, 8);
v_traceState_3595_ = lean_ctor_get(v___x_3586_, 9);
v_snapshotTasks_3596_ = lean_ctor_get(v___x_3586_, 10);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3586_, 1);
lean_dec(v_unused_3607_);
v___x_3598_ = v___x_3586_;
v_isShared_3599_ = v_isSharedCheck_3606_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_snapshotTasks_3596_);
lean_inc(v_traceState_3595_);
lean_inc(v_infoState_3594_);
lean_inc(v_auxDeclNGen_3593_);
lean_inc(v_ngen_3592_);
lean_inc(v_maxRecDepth_3591_);
lean_inc(v_nextMacroScope_3590_);
lean_inc(v_usedQuotCtxts_3589_);
lean_inc(v_scopes_3588_);
lean_inc(v_env_3587_);
lean_dec(v___x_3586_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3606_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v___y_3538_);
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_env_3587_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___y_3538_);
lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_scopes_3588_);
lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_usedQuotCtxts_3589_);
lean_ctor_set(v_reuseFailAlloc_3605_, 4, v_nextMacroScope_3590_);
lean_ctor_set(v_reuseFailAlloc_3605_, 5, v_maxRecDepth_3591_);
lean_ctor_set(v_reuseFailAlloc_3605_, 6, v_ngen_3592_);
lean_ctor_set(v_reuseFailAlloc_3605_, 7, v_auxDeclNGen_3593_);
lean_ctor_set(v_reuseFailAlloc_3605_, 8, v_infoState_3594_);
lean_ctor_set(v_reuseFailAlloc_3605_, 9, v_traceState_3595_);
lean_ctor_set(v_reuseFailAlloc_3605_, 10, v_snapshotTasks_3596_);
v___x_3601_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_st_ref_set(v___y_3543_, v___x_3601_);
v___x_3603_ = lean_box(0);
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
return v___x_3604_;
}
}
}
}
v___jp_3608_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_str_3631_; lean_object* v_startInclusive_3632_; lean_object* v_endExclusive_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3648_; 
v___x_3621_ = l_Lean_MessageLog_toList(v___y_3609_);
lean_dec(v___y_3609_);
v___x_3622_ = lean_box(0);
v___x_3623_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3620_, v___x_3621_, v___x_3622_);
lean_dec(v___y_3620_);
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v___x_3623_);
v___x_3625_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3614_, v_a_3624_);
v___x_3626_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3627_ = l_String_intercalate(v___x_3626_, v___x_3625_);
v___x_3628_ = lean_string_utf8_byte_size(v___x_3627_);
lean_inc(v___y_3613_);
v___x_3629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3627_);
lean_ctor_set(v___x_3629_, 1, v___y_3613_);
lean_ctor_set(v___x_3629_, 2, v___x_3628_);
v___x_3630_ = l_String_Slice_trimAscii(v___x_3629_);
v_str_3631_ = lean_ctor_get(v___x_3630_, 0);
v_startInclusive_3632_ = lean_ctor_get(v___x_3630_, 1);
v_endExclusive_3633_ = lean_ctor_get(v___x_3630_, 2);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3635_ = v___x_3630_;
v_isShared_3636_ = v_isSharedCheck_3648_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_endExclusive_3633_);
lean_inc(v_startInclusive_3632_);
lean_inc(v_str_3631_);
lean_dec(v___x_3630_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3648_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_string_utf8_extract(v_str_3631_, v_startInclusive_3632_, v_endExclusive_3633_);
lean_dec(v_endExclusive_3633_);
lean_dec(v_startInclusive_3632_);
lean_dec_ref(v_str_3631_);
if (v___y_3615_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
lean_del_object(v___x_3635_);
lean_inc_ref(v___y_3619_);
v___x_3638_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3610_, v___y_3619_);
lean_inc_ref(v___x_3637_);
v___x_3639_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3610_, v___x_3637_);
v___x_3640_ = lean_string_dec_eq(v___x_3638_, v___x_3639_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v___x_3638_);
v___y_3538_ = v___y_3612_;
v___y_3539_ = v___y_3611_;
v___y_3540_ = v___y_3613_;
v___y_3541_ = v___y_3616_;
v___y_3542_ = v___y_3617_;
v___y_3543_ = v___y_3618_;
v___y_3544_ = v___y_3619_;
v___y_3545_ = v___x_3637_;
v___y_3546_ = v___x_3640_;
goto v___jp_3537_;
}
else
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3645_; 
lean_inc_ref(v___x_3637_);
v___x_3641_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3610_, v___x_3637_);
lean_inc_ref(v___y_3619_);
v___x_3642_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3610_, v___y_3619_);
v___x_3643_ = lean_string_utf8_byte_size(v___x_3641_);
lean_inc(v___y_3613_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 2, v___x_3643_);
lean_ctor_set(v___x_3635_, 1, v___y_3613_);
lean_ctor_set(v___x_3635_, 0, v___x_3641_);
v___x_3645_ = v___x_3635_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v___y_3613_);
lean_ctor_set(v_reuseFailAlloc_3647_, 2, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
uint8_t v___x_3646_; 
v___x_3646_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3642_, v___x_3645_);
lean_dec_ref(v___x_3645_);
v___y_3538_ = v___y_3612_;
v___y_3539_ = v___y_3611_;
v___y_3540_ = v___y_3613_;
v___y_3541_ = v___y_3616_;
v___y_3542_ = v___y_3617_;
v___y_3543_ = v___y_3618_;
v___y_3544_ = v___y_3619_;
v___y_3545_ = v___x_3637_;
v___y_3546_ = v___x_3646_;
goto v___jp_3537_;
}
}
}
}
v___jp_3649_:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3651_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v_filterFn_3658_; uint8_t v_whitespace_3659_; uint8_t v_ordering_3660_; uint8_t v_reportPositions_3661_; uint8_t v_substring_3662_; lean_object* v___x_3663_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
v_filterFn_3658_ = lean_ctor_get(v_a_3657_, 0);
lean_inc_ref(v_filterFn_3658_);
v_whitespace_3659_ = lean_ctor_get_uint8(v_a_3657_, sizeof(void*)*1);
v_ordering_3660_ = lean_ctor_get_uint8(v_a_3657_, sizeof(void*)*1 + 1);
v_reportPositions_3661_ = lean_ctor_get_uint8(v_a_3657_, sizeof(void*)*1 + 2);
v_substring_3662_ = lean_ctor_get_uint8(v_a_3657_, sizeof(void*)*1 + 3);
lean_dec(v_a_3657_);
v___x_3663_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3650_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_a_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_str_3673_; lean_object* v_startInclusive_3674_; lean_object* v_endExclusive_3675_; lean_object* v_fst_3676_; lean_object* v_snd_3677_; lean_object* v_fileMap_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref(v___x_3663_);
v___x_3665_ = l_Lean_MessageLog_toList(v_a_3664_);
v___x_3666_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3667_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3658_, v___x_3665_, v___x_3666_);
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3667_);
v___x_3669_ = lean_unsigned_to_nat(0u);
v___x_3670_ = lean_string_utf8_byte_size(v___y_3655_);
v___x_3671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3671_, 0, v___y_3655_);
lean_ctor_set(v___x_3671_, 1, v___x_3669_);
lean_ctor_set(v___x_3671_, 2, v___x_3670_);
v___x_3672_ = l_String_Slice_trimAscii(v___x_3671_);
v_str_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc_ref(v_str_3673_);
v_startInclusive_3674_ = lean_ctor_get(v___x_3672_, 1);
lean_inc(v_startInclusive_3674_);
v_endExclusive_3675_ = lean_ctor_get(v___x_3672_, 2);
lean_inc(v_endExclusive_3675_);
lean_dec_ref(v___x_3672_);
v_fst_3676_ = lean_ctor_get(v_a_3668_, 0);
lean_inc(v_fst_3676_);
v_snd_3677_ = lean_ctor_get(v_a_3668_, 1);
lean_inc(v_snd_3677_);
lean_dec(v_a_3668_);
v_fileMap_3678_ = lean_ctor_get(v___y_3653_, 1);
v___x_3679_ = lean_string_utf8_extract(v_str_3673_, v_startInclusive_3674_, v_endExclusive_3675_);
lean_dec(v_endExclusive_3675_);
lean_dec(v_startInclusive_3674_);
lean_dec_ref(v_str_3673_);
v___x_3680_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3679_);
if (v_reportPositions_3661_ == 0)
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_box(0);
v___y_3609_ = v_fst_3676_;
v___y_3610_ = v_whitespace_3659_;
v___y_3611_ = v___y_3652_;
v___y_3612_ = v_snd_3677_;
v___y_3613_ = v___x_3669_;
v___y_3614_ = v_ordering_3660_;
v___y_3615_ = v_substring_3662_;
v___y_3616_ = v___y_3653_;
v___y_3617_ = v_a_3664_;
v___y_3618_ = v___y_3654_;
v___y_3619_ = v___x_3680_;
v___y_3620_ = v___x_3681_;
goto v___jp_3608_;
}
else
{
uint8_t v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = 0;
v___x_3683_ = l_Lean_Syntax_getPos_x3f(v___y_3652_, v___x_3682_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3684_; 
v___x_3684_ = lean_box(0);
v___y_3609_ = v_fst_3676_;
v___y_3610_ = v_whitespace_3659_;
v___y_3611_ = v___y_3652_;
v___y_3612_ = v_snd_3677_;
v___y_3613_ = v___x_3669_;
v___y_3614_ = v_ordering_3660_;
v___y_3615_ = v_substring_3662_;
v___y_3616_ = v___y_3653_;
v___y_3617_ = v_a_3664_;
v___y_3618_ = v___y_3654_;
v___y_3619_ = v___x_3680_;
v___y_3620_ = v___x_3684_;
goto v___jp_3608_;
}
else
{
lean_object* v_val_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3694_; 
v_val_3685_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3687_ = v___x_3683_;
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_val_3685_);
lean_dec(v___x_3683_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v_line_3690_; lean_object* v___x_3692_; 
lean_inc_ref(v_fileMap_3678_);
v___x_3689_ = l_Lean_FileMap_toPosition(v_fileMap_3678_, v_val_3685_);
lean_dec(v_val_3685_);
v_line_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_line_3690_);
lean_dec_ref(v___x_3689_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v_line_3690_);
v___x_3692_ = v___x_3687_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_line_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
v___y_3609_ = v_fst_3676_;
v___y_3610_ = v_whitespace_3659_;
v___y_3611_ = v___y_3652_;
v___y_3612_ = v_snd_3677_;
v___y_3613_ = v___x_3669_;
v___y_3614_ = v_ordering_3660_;
v___y_3615_ = v_substring_3662_;
v___y_3616_ = v___y_3653_;
v___y_3617_ = v_a_3664_;
v___y_3618_ = v___y_3654_;
v___y_3619_ = v___x_3680_;
v___y_3620_ = v___x_3692_;
goto v___jp_3608_;
}
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v_filterFn_3658_);
lean_dec_ref(v___y_3655_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
v_a_3695_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3663_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3663_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v___y_3655_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec(v___y_3650_);
v_a_3703_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3656_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3656_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
v___jp_3711_:
{
if (lean_obj_tag(v___y_3714_) == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
lean_inc_ref(v___y_3715_);
v___y_3650_ = v___y_3712_;
v___y_3651_ = v___y_3717_;
v___y_3652_ = v___y_3713_;
v___y_3653_ = v___y_3715_;
v___y_3654_ = v___y_3716_;
v___y_3655_ = v___x_3718_;
goto v___jp_3649_;
}
else
{
lean_object* v_val_3719_; lean_object* v___x_3720_; 
v_val_3719_ = lean_ctor_get(v___y_3714_, 0);
lean_inc(v_val_3719_);
lean_dec_ref(v___y_3714_);
v___x_3720_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3719_, v___y_3715_, v___y_3716_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref(v___x_3720_);
lean_inc_ref(v___y_3715_);
v___y_3650_ = v___y_3712_;
v___y_3651_ = v___y_3717_;
v___y_3652_ = v___y_3713_;
v___y_3653_ = v___y_3715_;
v___y_3654_ = v___y_3716_;
v___y_3655_ = v_a_3721_;
goto v___jp_3649_;
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v___y_3717_);
lean_dec(v___y_3713_);
lean_dec(v___y_3712_);
v_a_3722_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3720_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3720_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
v___jp_3730_:
{
lean_object* v___x_3734_; lean_object* v_tk_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3734_ = lean_unsigned_to_nat(1u);
v_tk_3735_ = l_Lean_Syntax_getArg(v_x_3501_, v___x_3734_);
v___x_3736_ = lean_unsigned_to_nat(2u);
v___x_3737_ = l_Lean_Syntax_getArg(v_x_3501_, v___x_3736_);
v___x_3738_ = lean_unsigned_to_nat(4u);
v___x_3739_ = l_Lean_Syntax_getArg(v_x_3501_, v___x_3738_);
lean_dec(v_x_3501_);
v___x_3740_ = l_Lean_Syntax_getOptional_x3f(v___x_3737_);
lean_dec(v___x_3737_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_box(0);
v___y_3712_ = v___x_3739_;
v___y_3713_ = v_tk_3735_;
v___y_3714_ = v_dc_x3f_3731_;
v___y_3715_ = v___y_3732_;
v___y_3716_ = v___y_3733_;
v___y_3717_ = v___x_3741_;
goto v___jp_3711_;
}
else
{
lean_object* v_val_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_val_3742_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3740_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_val_3742_);
lean_dec(v___x_3740_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_val_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
v___y_3712_ = v___x_3739_;
v___y_3713_ = v_tk_3735_;
v___y_3714_ = v_dc_x3f_3731_;
v___y_3715_ = v___y_3732_;
v___y_3716_ = v___y_3733_;
v___y_3717_ = v___x_3747_;
goto v___jp_3711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3770_, lean_object* v_as_3771_, lean_object* v_as_x27_3772_, lean_object* v_b_3773_, lean_object* v_a_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3770_, v_as_x27_3772_, v_b_3773_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3779_, lean_object* v_as_3780_, lean_object* v_as_x27_3781_, lean_object* v_b_3782_, lean_object* v_a_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3779_, v_as_3780_, v_as_x27_3781_, v_b_3782_, v_a_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v_as_3780_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3788_, lean_object* v_x_3789_, lean_object* v_x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3788_, v_x_3789_, v_x_3790_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3795_, lean_object* v_x_3796_, lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3795_, v_x_3796_, v_x_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3795_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3802_, v___y_3804_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3812_, lean_object* v___x_3813_, lean_object* v___x_3814_, lean_object* v_inst_3815_, lean_object* v_R_3816_, lean_object* v_a_3817_, lean_object* v_b_3818_){
_start:
{
lean_object* v___x_3819_; 
v___x_3819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3812_, v___x_3813_, v___x_3814_, v_a_3817_, v_b_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3820_, lean_object* v___x_3821_, lean_object* v___x_3822_, lean_object* v_inst_3823_, lean_object* v_R_3824_, lean_object* v_a_3825_, lean_object* v_b_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3820_, v___x_3821_, v___x_3822_, v_inst_3823_, v_R_3824_, v_a_3825_, v_b_3826_);
lean_dec_ref(v___x_3821_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3828_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v_inst_3841_, lean_object* v_R_3842_, lean_object* v_a_3843_, lean_object* v_b_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3838_, v___x_3839_, v___x_3840_, v_a_3843_, v_b_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v___x_3848_, lean_object* v_inst_3849_, lean_object* v_R_3850_, lean_object* v_a_3851_, lean_object* v_b_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3846_, v___x_3847_, v___x_3848_, v_inst_3849_, v_R_3850_, v_a_3851_, v_b_3852_);
lean_dec_ref(v___x_3847_);
return v_res_3853_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3854_, lean_object* v_inst_3855_, lean_object* v_R_3856_, lean_object* v_a_3857_, uint8_t v_b_3858_, lean_object* v_c_3859_){
_start:
{
uint8_t v___x_3860_; 
v___x_3860_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3854_, v_a_3857_, v_b_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3861_, lean_object* v_inst_3862_, lean_object* v_R_3863_, lean_object* v_a_3864_, lean_object* v_b_3865_, lean_object* v_c_3866_){
_start:
{
uint8_t v_b_boxed_3867_; uint8_t v_res_3868_; lean_object* v_r_3869_; 
v_b_boxed_3867_ = lean_unbox(v_b_3865_);
v_res_3868_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3861_, v_inst_3862_, v_R_3863_, v_a_3864_, v_b_boxed_3867_, v_c_3866_);
lean_dec_ref(v_s_3861_);
v_r_3869_ = lean_box(v_res_3868_);
return v_r_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3870_, lean_object* v_ref_3871_, lean_object* v_msg_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3871_, v_msg_3872_, v___y_3873_, v___y_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3877_, lean_object* v_ref_3878_, lean_object* v_msg_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3877_, v_ref_3878_, v_msg_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v_ref_3878_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3884_, lean_object* v_as_x27_3885_, lean_object* v_b_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3885_, v_b_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3889_, lean_object* v_as_x27_3890_, lean_object* v_b_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3889_, v_as_x27_3890_, v_b_3891_, v_a_3892_);
lean_dec(v_as_3889_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3894_, lean_object* v_rsize_3895_, lean_object* v_histogram_3896_, lean_object* v_index_3897_, lean_object* v_val_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3896_, v_index_3897_, v_val_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3900_, lean_object* v_rsize_3901_, lean_object* v_histogram_3902_, lean_object* v_index_3903_, lean_object* v_val_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3900_, v_rsize_3901_, v_histogram_3902_, v_index_3903_, v_val_3904_);
lean_dec(v_rsize_3901_);
lean_dec(v_lsize_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3906_, lean_object* v___x_3907_, lean_object* v_fst_3908_, lean_object* v___x_3909_, lean_object* v_inst_3910_, lean_object* v_R_3911_, lean_object* v_a_3912_, lean_object* v_b_3913_, lean_object* v_c_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3906_, v___x_3907_, v_fst_3908_, v___x_3909_, v_a_3912_, v_b_3913_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3916_, lean_object* v___x_3917_, lean_object* v_fst_3918_, lean_object* v___x_3919_, lean_object* v_inst_3920_, lean_object* v_R_3921_, lean_object* v_a_3922_, lean_object* v_b_3923_, lean_object* v_c_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3916_, v___x_3917_, v_fst_3918_, v___x_3919_, v_inst_3920_, v_R_3921_, v_a_3922_, v_b_3923_, v_c_3924_);
lean_dec(v___x_3919_);
lean_dec_ref(v_fst_3918_);
lean_dec(v___x_3917_);
lean_dec(v_upperBound_3916_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_3926_, lean_object* v_rsize_3927_, lean_object* v_histogram_3928_, lean_object* v_index_3929_, lean_object* v_val_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_3928_, v_index_3929_, v_val_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_3932_, lean_object* v_rsize_3933_, lean_object* v_histogram_3934_, lean_object* v_index_3935_, lean_object* v_val_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_3932_, v_rsize_3933_, v_histogram_3934_, v_index_3935_, v_val_3936_);
lean_dec(v_rsize_3933_);
lean_dec(v_lsize_3932_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_3938_, lean_object* v_fst_3939_, lean_object* v___x_3940_, lean_object* v_fst_3941_, lean_object* v_inst_3942_, lean_object* v_R_3943_, lean_object* v_a_3944_, lean_object* v_b_3945_, lean_object* v_c_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3938_, v_fst_3939_, v___x_3940_, v_fst_3941_, v_a_3944_, v_b_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_3948_, lean_object* v_fst_3949_, lean_object* v___x_3950_, lean_object* v_fst_3951_, lean_object* v_inst_3952_, lean_object* v_R_3953_, lean_object* v_a_3954_, lean_object* v_b_3955_, lean_object* v_c_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_3948_, v_fst_3949_, v___x_3950_, v_fst_3951_, v_inst_3952_, v_R_3953_, v_a_3954_, v_b_3955_, v_c_3956_);
lean_dec_ref(v_fst_3951_);
lean_dec(v___x_3950_);
lean_dec_ref(v_fst_3949_);
lean_dec(v_upperBound_3948_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_3958_, lean_object* v_msg_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; 
lean_inc_ref(v___y_3960_);
v___x_3963_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_3959_, v___y_3960_, v___y_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_3964_, lean_object* v_msg_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_3964_, v_msg_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_3970_, lean_object* v_m_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_3971_, v_a_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_3974_, lean_object* v_m_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_3974_, v_m_3975_, v_a_3976_);
lean_dec_ref(v_a_3976_);
lean_dec_ref(v_m_3975_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_3978_, lean_object* v_m_3979_, lean_object* v_a_3980_, lean_object* v_b_3981_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_3979_, v_a_3980_, v_b_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_3983_, lean_object* v_macroStack_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_3983_, v_macroStack_3984_, v___y_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_3989_, lean_object* v_macroStack_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_3989_, v_macroStack_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_3995_, lean_object* v_R_3996_, lean_object* v_a_3997_, lean_object* v_b_3998_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_3997_, v_b_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4000_, lean_object* v_a_4001_, lean_object* v_x_4002_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4001_, v_x_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4004_, lean_object* v_a_4005_, lean_object* v_x_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4004_, v_a_4005_, v_x_4006_);
lean_dec(v_x_4006_);
lean_dec_ref(v_a_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4008_, lean_object* v_a_4009_, lean_object* v_x_4010_){
_start:
{
uint8_t v___x_4011_; 
v___x_4011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4009_, v_x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4012_, lean_object* v_a_4013_, lean_object* v_x_4014_){
_start:
{
uint8_t v_res_4015_; lean_object* v_r_4016_; 
v_res_4015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4012_, v_a_4013_, v_x_4014_);
lean_dec(v_x_4014_);
lean_dec_ref(v_a_4013_);
v_r_4016_ = lean_box(v_res_4015_);
return v_r_4016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4017_, lean_object* v_data_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4020_, lean_object* v_a_4021_, lean_object* v_b_4022_, lean_object* v_x_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4021_, v_b_4022_, v_x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4025_, lean_object* v_i_4026_, lean_object* v_source_4027_, lean_object* v_target_4028_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4026_, v_source_4027_, v_target_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4030_, lean_object* v_x_4031_, lean_object* v_x_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4031_, v_x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4042_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4045_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4046_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4042_, v___x_4043_, v___x_4044_, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4076_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4077_ = l_Lean_addBuiltinDeclarationRanges(v___x_4075_, v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4080_){
_start:
{
lean_object* v_doc_4082_; lean_object* v___x_4083_; 
v_doc_4082_ = lean_ctor_get(v___y_4080_, 1);
lean_inc_ref(v_doc_4082_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_doc_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4084_);
lean_dec_ref(v___y_4084_);
return v_res_4086_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4087_, lean_object* v_a_4088_, uint8_t v_b_4089_){
_start:
{
lean_object* v_str_4090_; lean_object* v_startInclusive_4091_; lean_object* v_endExclusive_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v_str_4090_ = lean_ctor_get(v_s_4087_, 0);
v_startInclusive_4091_ = lean_ctor_get(v_s_4087_, 1);
v_endExclusive_4092_ = lean_ctor_get(v_s_4087_, 2);
v___x_4093_ = lean_nat_sub(v_endExclusive_4092_, v_startInclusive_4091_);
v___x_4094_ = lean_nat_dec_eq(v_a_4088_, v___x_4093_);
lean_dec(v___x_4093_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; uint32_t v___x_4096_; uint32_t v___x_4097_; uint8_t v___x_4098_; 
v___x_4095_ = lean_nat_add(v_startInclusive_4091_, v_a_4088_);
lean_dec(v_a_4088_);
v___x_4096_ = lean_string_utf8_get_fast(v_str_4090_, v___x_4095_);
v___x_4097_ = 10;
v___x_4098_ = lean_uint32_dec_eq(v___x_4096_, v___x_4097_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_string_utf8_next_fast(v_str_4090_, v___x_4095_);
lean_dec(v___x_4095_);
v___x_4100_ = lean_nat_sub(v___x_4099_, v_startInclusive_4091_);
v_a_4088_ = v___x_4100_;
v_b_4089_ = v___x_4098_;
goto _start;
}
else
{
lean_dec(v___x_4095_);
return v___x_4098_;
}
}
else
{
lean_dec(v_a_4088_);
return v_b_4089_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4102_, lean_object* v_a_4103_, lean_object* v_b_4104_){
_start:
{
uint8_t v_b_boxed_4105_; uint8_t v_res_4106_; lean_object* v_r_4107_; 
v_b_boxed_4105_ = lean_unbox(v_b_4104_);
v_res_4106_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4102_, v_a_4103_, v_b_boxed_4105_);
lean_dec_ref(v_s_4102_);
v_r_4107_ = lean_box(v_res_4106_);
return v_r_4107_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4108_){
_start:
{
lean_object* v_searcher_4109_; uint8_t v___x_4110_; uint8_t v___x_4111_; 
v_searcher_4109_ = lean_unsigned_to_nat(0u);
v___x_4110_ = 0;
v___x_4111_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4108_, v_searcher_4109_, v___x_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4112_){
_start:
{
uint8_t v_res_4113_; lean_object* v_r_4114_; 
v_res_4113_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4112_);
lean_dec_ref(v_s_4112_);
v_r_4114_ = lean_box(v_res_4113_);
return v_r_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4126_, lean_object* v_fst_4127_, uint8_t v___x_4128_, lean_object* v_a_4129_, lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v___x_4132_, lean_object* v___x_4133_, lean_object* v___x_4134_, lean_object* v___x_4135_, lean_object* v___x_4136_, lean_object* v___x_4137_, lean_object* v_snd_4138_, lean_object* v___x_4139_){
_start:
{
if (lean_obj_tag(v___x_4126_) == 1)
{
lean_object* v_val_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4204_; 
v_val_4141_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4143_ = v___x_4126_;
v_isShared_4144_ = v_isSharedCheck_4204_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_val_4141_);
lean_dec(v___x_4126_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4204_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4145_ = lean_unsigned_to_nat(0u);
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4147_ = l_Lean_Syntax_setArg(v_fst_4127_, v___x_4145_, v___x_4146_);
v___x_4148_ = l_Lean_Syntax_getPos_x3f(v___x_4147_, v___x_4128_);
lean_dec(v___x_4147_);
if (lean_obj_tag(v___x_4148_) == 1)
{
lean_object* v_val_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4200_; 
lean_dec_ref(v___x_4139_);
v_val_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4200_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_val_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4200_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___y_4154_; lean_object* v___x_4180_; uint8_t v___y_4187_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4180_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4138_);
v___x_4192_ = lean_string_utf8_byte_size(v___x_4180_);
v___x_4193_ = lean_nat_dec_eq(v___x_4192_, v___x_4145_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4194_ = lean_string_length(v___x_4180_);
v___x_4195_ = lean_unsigned_to_nat(93u);
v___x_4196_ = lean_nat_dec_le(v___x_4194_, v___x_4195_);
if (v___x_4196_ == 0)
{
v___y_4187_ = v___x_4196_;
goto v___jp_4186_;
}
else
{
lean_object* v___x_4197_; uint8_t v___x_4198_; 
lean_inc_ref(v___x_4180_);
v___x_4197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4180_);
lean_ctor_set(v___x_4197_, 1, v___x_4145_);
lean_ctor_set(v___x_4197_, 2, v___x_4192_);
v___x_4198_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4197_);
lean_dec_ref(v___x_4197_);
if (v___x_4198_ == 0)
{
v___y_4187_ = v___x_4196_;
goto v___jp_4186_;
}
else
{
goto v___jp_4181_;
}
}
}
else
{
lean_object* v___x_4199_; 
lean_dec_ref(v___x_4180_);
v___x_4199_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4154_ = v___x_4199_;
goto v___jp_4153_;
}
v___jp_4153_:
{
lean_object* v_toEditableDocumentCore_4155_; lean_object* v_meta_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4176_; 
v_toEditableDocumentCore_4155_ = lean_ctor_get(v_a_4129_, 0);
lean_inc_ref(v_toEditableDocumentCore_4155_);
v_meta_4156_ = lean_ctor_get(v_toEditableDocumentCore_4155_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_toEditableDocumentCore_4155_);
if (v_isSharedCheck_4176_ == 0)
{
lean_object* v_unused_4177_; lean_object* v_unused_4178_; lean_object* v_unused_4179_; 
v_unused_4177_ = lean_ctor_get(v_toEditableDocumentCore_4155_, 3);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_toEditableDocumentCore_4155_, 2);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_toEditableDocumentCore_4155_, 1);
lean_dec(v_unused_4179_);
v___x_4158_ = v_toEditableDocumentCore_4155_;
v_isShared_4159_ = v_isSharedCheck_4176_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_meta_4156_);
lean_dec(v_toEditableDocumentCore_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4176_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_text_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v_text_4160_ = lean_ctor_get(v_meta_4156_, 3);
lean_inc_ref(v_text_4160_);
lean_dec_ref(v_meta_4156_);
v___x_4161_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4129_);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v_val_4141_);
lean_ctor_set(v___x_4162_, 1, v_val_4149_);
v___x_4163_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4160_, v___x_4162_);
v___x_4164_ = lean_box(0);
lean_inc(v___x_4130_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 3, v___x_4130_);
lean_ctor_set(v___x_4158_, 2, v___x_4164_);
lean_ctor_set(v___x_4158_, 1, v___y_4154_);
lean_ctor_set(v___x_4158_, 0, v___x_4163_);
v___x_4166_ = v___x_4158_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___y_4154_);
lean_ctor_set(v_reuseFailAlloc_4175_, 2, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4175_, 3, v___x_4130_);
v___x_4166_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4167_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4161_, v___x_4166_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4167_);
v___x_4169_ = v___x_4151_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_inc(v___x_4130_);
v___x_4170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4130_);
lean_ctor_set(v___x_4170_, 1, v___x_4130_);
lean_ctor_set(v___x_4170_, 2, v___x_4131_);
lean_ctor_set(v___x_4170_, 3, v___x_4132_);
lean_ctor_set(v___x_4170_, 4, v___x_4133_);
lean_ctor_set(v___x_4170_, 5, v___x_4134_);
lean_ctor_set(v___x_4170_, 6, v___x_4135_);
lean_ctor_set(v___x_4170_, 7, v___x_4169_);
lean_ctor_set(v___x_4170_, 8, v___x_4136_);
lean_ctor_set(v___x_4170_, 9, v___x_4137_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4170_);
v___x_4172_ = v___x_4143_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
v___jp_4181_:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4182_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4183_ = lean_string_append(v___x_4182_, v___x_4180_);
lean_dec_ref(v___x_4180_);
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4185_ = lean_string_append(v___x_4183_, v___x_4184_);
v___y_4154_ = v___x_4185_;
goto v___jp_4153_;
}
v___jp_4186_:
{
if (v___y_4187_ == 0)
{
goto v___jp_4181_;
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4188_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4189_ = lean_string_append(v___x_4188_, v___x_4180_);
lean_dec_ref(v___x_4180_);
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4191_ = lean_string_append(v___x_4189_, v___x_4190_);
v___y_4154_ = v___x_4191_;
goto v___jp_4153_;
}
}
}
}
else
{
lean_object* v___x_4202_; 
lean_dec(v___x_4148_);
lean_dec(v_val_4141_);
lean_dec_ref(v_snd_4138_);
lean_dec(v___x_4137_);
lean_dec(v___x_4136_);
lean_dec(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v___x_4133_);
lean_dec(v___x_4132_);
lean_dec_ref(v___x_4131_);
lean_dec(v___x_4130_);
lean_dec_ref(v_a_4129_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4139_);
v___x_4202_ = v___x_4143_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4139_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
else
{
lean_object* v___x_4205_; 
lean_dec_ref(v_snd_4138_);
lean_dec(v___x_4137_);
lean_dec(v___x_4136_);
lean_dec(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v___x_4133_);
lean_dec(v___x_4132_);
lean_dec_ref(v___x_4131_);
lean_dec(v___x_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_fst_4127_);
lean_dec(v___x_4126_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4139_);
return v___x_4205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4206_, lean_object* v_fst_4207_, lean_object* v___x_4208_, lean_object* v_a_4209_, lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v___x_4214_, lean_object* v___x_4215_, lean_object* v___x_4216_, lean_object* v___x_4217_, lean_object* v_snd_4218_, lean_object* v___x_4219_, lean_object* v___y_4220_){
_start:
{
uint8_t v___x_4549__boxed_4221_; lean_object* v_res_4222_; 
v___x_4549__boxed_4221_ = lean_unbox(v___x_4208_);
v_res_4222_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4206_, v_fst_4207_, v___x_4549__boxed_4221_, v_a_4209_, v___x_4210_, v___x_4211_, v___x_4212_, v___x_4213_, v___x_4214_, v___x_4215_, v___x_4216_, v___x_4217_, v_snd_4218_, v___x_4219_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4226_, size_t v_sz_4227_, size_t v_i_4228_, lean_object* v_b_4229_){
_start:
{
lean_object* v_a_4231_; uint8_t v___x_4235_; 
v___x_4235_ = lean_usize_dec_lt(v_i_4228_, v_sz_4227_);
if (v___x_4235_ == 0)
{
return v_b_4229_;
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_a_4238_; 
lean_dec_ref(v_b_4229_);
v___x_4236_ = lean_box(0);
v___x_4237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4238_ = lean_array_uget(v_as_4226_, v_i_4228_);
if (lean_obj_tag(v_a_4238_) == 1)
{
lean_object* v_i_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4273_; 
v_i_4239_ = lean_ctor_get(v_a_4238_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_a_4238_);
if (v_isSharedCheck_4273_ == 0)
{
lean_object* v_unused_4274_; 
v_unused_4274_ = lean_ctor_get(v_a_4238_, 1);
lean_dec(v_unused_4274_);
v___x_4241_ = v_a_4238_;
v_isShared_4242_ = v_isSharedCheck_4273_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_i_4239_);
lean_dec(v_a_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4273_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
if (lean_obj_tag(v_i_4239_) == 10)
{
lean_object* v_i_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4272_; 
v_i_4243_ = lean_ctor_get(v_i_4239_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_i_4239_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4245_ = v_i_4239_;
v_isShared_4246_ = v_isSharedCheck_4272_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_i_4243_);
lean_dec(v_i_4239_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4272_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v_stx_4247_; lean_object* v_value_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4271_; 
v_stx_4247_ = lean_ctor_get(v_i_4243_, 0);
v_value_4248_ = lean_ctor_get(v_i_4243_, 1);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_i_4243_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4250_ = v_i_4243_;
v_isShared_4251_ = v_isSharedCheck_4271_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_value_4248_);
lean_inc(v_stx_4247_);
lean_dec(v_i_4243_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4271_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4253_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4248_, v___x_4252_);
lean_dec(v_value_4248_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_del_object(v___x_4250_);
lean_dec(v_stx_4247_);
lean_del_object(v___x_4245_);
lean_del_object(v___x_4241_);
v_a_4231_ = v___x_4237_;
goto v___jp_4230_;
}
else
{
lean_object* v_val_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4270_; 
v_val_4254_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4256_ = v___x_4253_;
v_isShared_4257_ = v_isSharedCheck_4270_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_val_4254_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4270_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 1, v_val_4254_);
v___x_4259_ = v___x_4250_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_stx_4247_);
lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_val_4254_);
v___x_4259_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4261_; 
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4259_);
v___x_4261_ = v___x_4256_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4263_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 1);
lean_ctor_set(v___x_4245_, 0, v___x_4261_);
v___x_4263_ = v___x_4245_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4265_; 
if (v_isShared_4242_ == 0)
{
lean_ctor_set_tag(v___x_4241_, 0);
lean_ctor_set(v___x_4241_, 1, v___x_4236_);
lean_ctor_set(v___x_4241_, 0, v___x_4263_);
v___x_4265_ = v___x_4241_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v___x_4236_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
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
lean_del_object(v___x_4241_);
lean_dec_ref(v_i_4239_);
v_a_4231_ = v___x_4237_;
goto v___jp_4230_;
}
}
}
else
{
lean_dec(v_a_4238_);
v_a_4231_ = v___x_4237_;
goto v___jp_4230_;
}
}
v___jp_4230_:
{
size_t v___x_4232_; size_t v___x_4233_; 
v___x_4232_ = ((size_t)1ULL);
v___x_4233_ = lean_usize_add(v_i_4228_, v___x_4232_);
v_i_4228_ = v___x_4233_;
v_b_4229_ = v_a_4231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4275_, lean_object* v_sz_4276_, lean_object* v_i_4277_, lean_object* v_b_4278_){
_start:
{
size_t v_sz_boxed_4279_; size_t v_i_boxed_4280_; lean_object* v_res_4281_; 
v_sz_boxed_4279_ = lean_unbox_usize(v_sz_4276_);
lean_dec(v_sz_4276_);
v_i_boxed_4280_ = lean_unbox_usize(v_i_4277_);
lean_dec(v_i_4277_);
v_res_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4275_, v_sz_boxed_4279_, v_i_boxed_4280_, v_b_4278_);
lean_dec_ref(v_as_4275_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4282_, size_t v_sz_4283_, size_t v_i_4284_, lean_object* v_b_4285_){
_start:
{
lean_object* v_a_4287_; uint8_t v___x_4291_; 
v___x_4291_ = lean_usize_dec_lt(v_i_4284_, v_sz_4283_);
if (v___x_4291_ == 0)
{
lean_inc_ref(v_b_4285_);
return v_b_4285_;
}
else
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v_a_4294_; 
v___x_4292_ = lean_box(0);
v___x_4293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4294_ = lean_array_uget(v_as_4282_, v_i_4284_);
if (lean_obj_tag(v_a_4294_) == 1)
{
lean_object* v_i_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4329_; 
v_i_4295_ = lean_ctor_get(v_a_4294_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v_a_4294_);
if (v_isSharedCheck_4329_ == 0)
{
lean_object* v_unused_4330_; 
v_unused_4330_ = lean_ctor_get(v_a_4294_, 1);
lean_dec(v_unused_4330_);
v___x_4297_ = v_a_4294_;
v_isShared_4298_ = v_isSharedCheck_4329_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_i_4295_);
lean_dec(v_a_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4329_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
if (lean_obj_tag(v_i_4295_) == 10)
{
lean_object* v_i_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4328_; 
v_i_4299_ = lean_ctor_get(v_i_4295_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v_i_4295_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4301_ = v_i_4295_;
v_isShared_4302_ = v_isSharedCheck_4328_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_i_4299_);
lean_dec(v_i_4295_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4328_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v_stx_4303_; lean_object* v_value_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4327_; 
v_stx_4303_ = lean_ctor_get(v_i_4299_, 0);
v_value_4304_ = lean_ctor_get(v_i_4299_, 1);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_i_4299_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4306_ = v_i_4299_;
v_isShared_4307_ = v_isSharedCheck_4327_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_value_4304_);
lean_inc(v_stx_4303_);
lean_dec(v_i_4299_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4327_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4309_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4304_, v___x_4308_);
lean_dec(v_value_4304_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_del_object(v___x_4306_);
lean_dec(v_stx_4303_);
lean_del_object(v___x_4301_);
lean_del_object(v___x_4297_);
v_a_4287_ = v___x_4293_;
goto v___jp_4286_;
}
else
{
lean_object* v_val_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4326_; 
v_val_4310_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4312_ = v___x_4309_;
v_isShared_4313_ = v_isSharedCheck_4326_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_val_4310_);
lean_dec(v___x_4309_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4326_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 1, v_val_4310_);
v___x_4315_ = v___x_4306_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_stx_4303_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_val_4310_);
v___x_4315_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4317_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v___x_4315_);
v___x_4317_ = v___x_4312_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4315_);
v___x_4317_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
lean_object* v___x_4319_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set_tag(v___x_4301_, 1);
lean_ctor_set(v___x_4301_, 0, v___x_4317_);
v___x_4319_ = v___x_4301_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4321_; 
if (v_isShared_4298_ == 0)
{
lean_ctor_set_tag(v___x_4297_, 0);
lean_ctor_set(v___x_4297_, 1, v___x_4292_);
lean_ctor_set(v___x_4297_, 0, v___x_4319_);
v___x_4321_ = v___x_4297_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4319_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4292_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
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
lean_del_object(v___x_4297_);
lean_dec_ref(v_i_4295_);
v_a_4287_ = v___x_4293_;
goto v___jp_4286_;
}
}
}
else
{
lean_dec(v_a_4294_);
v_a_4287_ = v___x_4293_;
goto v___jp_4286_;
}
}
v___jp_4286_:
{
size_t v___x_4288_; size_t v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = ((size_t)1ULL);
v___x_4289_ = lean_usize_add(v_i_4284_, v___x_4288_);
v___x_4290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4282_, v_sz_4283_, v___x_4289_, v_a_4287_);
return v___x_4290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4331_, lean_object* v_sz_4332_, lean_object* v_i_4333_, lean_object* v_b_4334_){
_start:
{
size_t v_sz_boxed_4335_; size_t v_i_boxed_4336_; lean_object* v_res_4337_; 
v_sz_boxed_4335_ = lean_unbox_usize(v_sz_4332_);
lean_dec(v_sz_4332_);
v_i_boxed_4336_ = lean_unbox_usize(v_i_4333_);
lean_dec(v_i_4333_);
v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4331_, v_sz_boxed_4335_, v_i_boxed_4336_, v_b_4334_);
lean_dec_ref(v_b_4334_);
lean_dec_ref(v_as_4331_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4338_){
_start:
{
if (lean_obj_tag(v_x_4338_) == 0)
{
lean_object* v_cs_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; size_t v_sz_4342_; size_t v___x_4343_; lean_object* v___x_4344_; lean_object* v_fst_4345_; 
v_cs_4339_ = lean_ctor_get(v_x_4338_, 0);
v___x_4340_ = lean_box(0);
v___x_4341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4342_ = lean_array_size(v_cs_4339_);
v___x_4343_ = ((size_t)0ULL);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4339_, v_sz_4342_, v___x_4343_, v___x_4341_);
v_fst_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_fst_4345_);
lean_dec_ref(v___x_4344_);
if (lean_obj_tag(v_fst_4345_) == 0)
{
return v___x_4340_;
}
else
{
lean_object* v_val_4346_; 
v_val_4346_ = lean_ctor_get(v_fst_4345_, 0);
lean_inc(v_val_4346_);
lean_dec_ref(v_fst_4345_);
return v_val_4346_;
}
}
else
{
lean_object* v_vs_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; size_t v_sz_4350_; size_t v___x_4351_; lean_object* v___x_4352_; lean_object* v_fst_4353_; 
v_vs_4347_ = lean_ctor_get(v_x_4338_, 0);
v___x_4348_ = lean_box(0);
v___x_4349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4350_ = lean_array_size(v_vs_4347_);
v___x_4351_ = ((size_t)0ULL);
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4347_, v_sz_4350_, v___x_4351_, v___x_4349_);
v_fst_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_fst_4353_);
lean_dec_ref(v___x_4352_);
if (lean_obj_tag(v_fst_4353_) == 0)
{
return v___x_4348_;
}
else
{
lean_object* v_val_4354_; 
v_val_4354_ = lean_ctor_get(v_fst_4353_, 0);
lean_inc(v_val_4354_);
lean_dec_ref(v_fst_4353_);
return v_val_4354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4355_, size_t v_sz_4356_, size_t v_i_4357_, lean_object* v_b_4358_){
_start:
{
uint8_t v___x_4359_; 
v___x_4359_ = lean_usize_dec_lt(v_i_4357_, v_sz_4356_);
if (v___x_4359_ == 0)
{
return v_b_4358_;
}
else
{
lean_object* v___x_4360_; lean_object* v_a_4361_; lean_object* v___x_4362_; 
lean_dec_ref(v_b_4358_);
v___x_4360_ = lean_box(0);
v_a_4361_ = lean_array_uget_borrowed(v_as_4355_, v_i_4357_);
v___x_4362_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4361_);
if (lean_obj_tag(v___x_4362_) == 1)
{
lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
lean_ctor_set(v___x_4364_, 1, v___x_4360_);
return v___x_4364_;
}
else
{
lean_object* v___x_4365_; size_t v___x_4366_; size_t v___x_4367_; 
lean_dec(v___x_4362_);
v___x_4365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4366_ = ((size_t)1ULL);
v___x_4367_ = lean_usize_add(v_i_4357_, v___x_4366_);
v_i_4357_ = v___x_4367_;
v_b_4358_ = v___x_4365_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4369_, lean_object* v_sz_4370_, lean_object* v_i_4371_, lean_object* v_b_4372_){
_start:
{
size_t v_sz_boxed_4373_; size_t v_i_boxed_4374_; lean_object* v_res_4375_; 
v_sz_boxed_4373_ = lean_unbox_usize(v_sz_4370_);
lean_dec(v_sz_4370_);
v_i_boxed_4374_ = lean_unbox_usize(v_i_4371_);
lean_dec(v_i_4371_);
v_res_4375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4369_, v_sz_boxed_4373_, v_i_boxed_4374_, v_b_4372_);
lean_dec_ref(v_as_4369_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4376_);
lean_dec_ref(v_x_4376_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4378_){
_start:
{
lean_object* v_root_4379_; lean_object* v_tail_4380_; lean_object* v___x_4381_; 
v_root_4379_ = lean_ctor_get(v_t_4378_, 0);
v_tail_4380_ = lean_ctor_get(v_t_4378_, 1);
v___x_4381_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4379_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v___x_4382_; size_t v_sz_4383_; size_t v___x_4384_; lean_object* v___x_4385_; lean_object* v_fst_4386_; 
v___x_4382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4383_ = lean_array_size(v_tail_4380_);
v___x_4384_ = ((size_t)0ULL);
v___x_4385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4380_, v_sz_4383_, v___x_4384_, v___x_4382_);
v_fst_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_fst_4386_);
lean_dec_ref(v___x_4385_);
if (lean_obj_tag(v_fst_4386_) == 0)
{
return v___x_4381_;
}
else
{
lean_object* v_val_4387_; 
v_val_4387_ = lean_ctor_get(v_fst_4386_, 0);
lean_inc(v_val_4387_);
lean_dec_ref(v_fst_4386_);
return v_val_4387_;
}
}
else
{
return v___x_4381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4388_);
lean_dec_ref(v_t_4388_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4404_, lean_object* v_a_4405_){
_start:
{
if (lean_obj_tag(v_node_4404_) == 1)
{
lean_object* v_children_4407_; lean_object* v_res_4408_; 
v_children_4407_ = lean_ctor_get(v_node_4404_, 1);
v_res_4408_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4407_);
if (lean_obj_tag(v_res_4408_) == 1)
{
lean_object* v_val_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4446_; 
v_val_4409_ = lean_ctor_get(v_res_4408_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v_res_4408_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4411_ = v_res_4408_;
v_isShared_4412_ = v_isSharedCheck_4446_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_val_4409_);
lean_dec(v_res_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4446_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v_fst_4413_; lean_object* v_snd_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4445_; 
v_fst_4413_ = lean_ctor_get(v_val_4409_, 0);
v_snd_4414_ = lean_ctor_get(v_val_4409_, 1);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_val_4409_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4416_ = v_val_4409_;
v_isShared_4417_ = v_isSharedCheck_4445_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_snd_4414_);
lean_inc(v_fst_4413_);
lean_dec(v_val_4409_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4445_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4444_; 
v___x_4418_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4405_);
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4444_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4444_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; uint8_t v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___y_4431_; lean_object* v___x_4433_; 
v___x_4423_ = lean_box(0);
v___x_4424_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4425_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4426_ = 1;
v___x_4427_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4428_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4429_ = l_Lean_Syntax_getPos_x3f(v_fst_4413_, v___x_4426_);
v___x_4430_ = lean_box(v___x_4426_);
v___y_4431_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4431_, 0, v___x_4429_);
lean_closure_set(v___y_4431_, 1, v_fst_4413_);
lean_closure_set(v___y_4431_, 2, v___x_4430_);
lean_closure_set(v___y_4431_, 3, v_a_4419_);
lean_closure_set(v___y_4431_, 4, v___x_4423_);
lean_closure_set(v___y_4431_, 5, v___x_4424_);
lean_closure_set(v___y_4431_, 6, v___x_4425_);
lean_closure_set(v___y_4431_, 7, v___x_4423_);
lean_closure_set(v___y_4431_, 8, v___x_4427_);
lean_closure_set(v___y_4431_, 9, v___x_4423_);
lean_closure_set(v___y_4431_, 10, v___x_4423_);
lean_closure_set(v___y_4431_, 11, v___x_4423_);
lean_closure_set(v___y_4431_, 12, v_snd_4414_);
lean_closure_set(v___y_4431_, 13, v___x_4428_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v___y_4431_);
v___x_4433_ = v___x_4411_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___y_4431_);
v___x_4433_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4435_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 1, v___x_4433_);
lean_ctor_set(v___x_4416_, 0, v___x_4428_);
v___x_4435_ = v___x_4416_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4428_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4436_ = lean_unsigned_to_nat(1u);
v___x_4437_ = lean_mk_empty_array_with_capacity(v___x_4436_);
v___x_4438_ = lean_array_push(v___x_4437_, v___x_4435_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4438_);
v___x_4440_ = v___x_4421_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4438_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
lean_dec(v_res_4408_);
v___x_4447_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
return v___x_4448_;
}
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
return v___x_4450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4451_, v_a_4452_);
lean_dec_ref(v_a_4452_);
lean_dec_ref(v_node_4451_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4455_, lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v_node_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v___x_4461_; 
v___x_4461_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4458_, v_a_4459_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4462_, lean_object* v_x_4463_, lean_object* v_x_4464_, lean_object* v_node_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4462_, v_x_4463_, v_x_4464_, v_node_4465_, v_a_4466_);
lean_dec_ref(v_a_4466_);
lean_dec_ref(v_node_4465_);
lean_dec_ref(v_x_4464_);
lean_dec_ref(v_x_4463_);
lean_dec_ref(v_x_4462_);
return v_res_4468_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4469_, lean_object* v_inst_4470_, lean_object* v_R_4471_, lean_object* v_a_4472_, uint8_t v_b_4473_, lean_object* v_c_4474_){
_start:
{
uint8_t v___x_4475_; 
v___x_4475_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4469_, v_a_4472_, v_b_4473_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4476_, lean_object* v_inst_4477_, lean_object* v_R_4478_, lean_object* v_a_4479_, lean_object* v_b_4480_, lean_object* v_c_4481_){
_start:
{
uint8_t v_b_boxed_4482_; uint8_t v_res_4483_; lean_object* v_r_4484_; 
v_b_boxed_4482_ = lean_unbox(v_b_4480_);
v_res_4483_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4476_, v_inst_4477_, v_R_4478_, v_a_4479_, v_b_boxed_4482_, v_c_4481_);
lean_dec_ref(v_s_4476_);
v_r_4484_ = lean_box(v_res_4483_);
return v_r_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_(){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_));
v___x_4491_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4492_ = l_Lean_CodeAction_insertBuiltin(v___x_4490_, v___x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369____boxed(lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
return v_res_4494_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4496_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4497_ = lean_string_utf8_byte_size(v___x_4496_);
return v___x_4497_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4500_ = lean_nat_dec_eq(v___x_4499_, v___x_4498_);
return v___x_4500_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4501_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4502_ = lean_unsigned_to_nat(0u);
v___x_4503_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v___x_4502_);
lean_ctor_set(v___x_4504_, 2, v___x_4501_);
return v___x_4504_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4506_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4505_);
return v___x_4506_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4507_ = lean_unsigned_to_nat(0u);
v___x_4508_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4509_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4510_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
lean_ctor_set(v___x_4510_, 1, v___x_4508_);
lean_ctor_set(v___x_4510_, 2, v___x_4507_);
lean_ctor_set(v___x_4510_, 3, v___x_4507_);
return v___x_4510_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4511_){
_start:
{
lean_object* v___y_4513_; uint8_t v___x_4516_; 
v___x_4516_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; 
v___x_4517_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4513_ = v___x_4517_;
goto v___jp_4512_;
}
else
{
lean_object* v___x_4518_; 
v___x_4518_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4513_ = v___x_4518_;
goto v___jp_4512_;
}
v___jp_4512_:
{
uint8_t v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = 0;
v___x_4515_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4511_, v___y_4513_, v___x_4514_);
return v___x_4515_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4519_){
_start:
{
uint8_t v_res_4520_; lean_object* v_r_4521_; 
v_res_4520_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4519_);
lean_dec_ref(v_s_4519_);
v_r_4521_ = lean_box(v_res_4520_);
return v_r_4521_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4522_, lean_object* v_as_x27_4523_, uint8_t v_b_4524_){
_start:
{
if (lean_obj_tag(v_as_x27_4523_) == 0)
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = lean_box(v_b_4524_);
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
return v___x_4527_;
}
else
{
lean_object* v_head_4528_; uint8_t v_isSilent_4529_; 
v_head_4528_ = lean_ctor_get(v_as_x27_4523_, 0);
v_isSilent_4529_ = lean_ctor_get_uint8(v_head_4528_, sizeof(void*)*5 + 2);
if (v_isSilent_4529_ == 0)
{
lean_object* v_tail_4530_; lean_object* v_data_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; 
lean_inc(v_head_4528_);
v_tail_4530_ = lean_ctor_get(v_as_x27_4523_, 1);
lean_inc(v_tail_4530_);
lean_dec_ref(v_as_x27_4523_);
v_data_4531_ = lean_ctor_get(v_head_4528_, 4);
lean_inc(v_data_4531_);
lean_dec(v_head_4528_);
v___x_4532_ = l_Lean_MessageData_toString(v_data_4531_);
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = lean_string_utf8_byte_size(v___x_4532_);
v___x_4535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4532_);
lean_ctor_set(v___x_4535_, 1, v___x_4533_);
lean_ctor_set(v___x_4535_, 2, v___x_4534_);
v___x_4536_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4535_);
lean_dec_ref(v___x_4535_);
if (v___x_4536_ == 0)
{
v_as_x27_4523_ = v_tail_4530_;
goto _start;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
lean_dec(v_tail_4530_);
v___x_4538_ = lean_box(v_foundPanic_4522_);
v___x_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
return v___x_4539_;
}
}
else
{
lean_object* v_tail_4540_; 
v_tail_4540_ = lean_ctor_get(v_as_x27_4523_, 1);
lean_inc(v_tail_4540_);
lean_dec_ref(v_as_x27_4523_);
v_as_x27_4523_ = v_tail_4540_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4542_, lean_object* v_as_x27_4543_, lean_object* v_b_4544_, lean_object* v___y_4545_){
_start:
{
uint8_t v_foundPanic_boxed_4546_; uint8_t v_b_boxed_4547_; lean_object* v_res_4548_; 
v_foundPanic_boxed_4546_ = lean_unbox(v_foundPanic_4542_);
v_b_boxed_4547_ = lean_unbox(v_b_4544_);
v_res_4548_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4546_, v_as_x27_4543_, v_b_boxed_4547_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4549_, uint8_t v_severity_4550_, uint8_t v_isSilent_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = l_Lean_Elab_Command_getRef___redArg(v___y_4552_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
lean_inc_ref(v___y_4552_);
v___x_4557_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4556_, v_msgData_4549_, v_severity_4550_, v_isSilent_4551_, v___y_4552_, v___y_4553_);
lean_dec(v_a_4556_);
return v___x_4557_;
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref(v_msgData_4549_);
v_a_4558_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4555_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4555_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4566_, lean_object* v_severity_4567_, lean_object* v_isSilent_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
uint8_t v_severity_boxed_4572_; uint8_t v_isSilent_boxed_4573_; lean_object* v_res_4574_; 
v_severity_boxed_4572_ = lean_unbox(v_severity_4567_);
v_isSilent_boxed_4573_ = lean_unbox(v_isSilent_4568_);
v_res_4574_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4566_, v_severity_boxed_4572_, v_isSilent_boxed_4573_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
uint8_t v___x_4579_; uint8_t v___x_4580_; lean_object* v___x_4581_; 
v___x_4579_ = 2;
v___x_4580_ = 0;
v___x_4581_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4575_, v___x_4579_, v___x_4580_, v___y_4576_, v___y_4577_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4586_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4595_ = l_Lean_MessageData_ofFormat(v___x_4594_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v___x_4600_; uint8_t v_foundPanic_4601_; 
v___x_4600_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4596_);
v_foundPanic_4601_ = l_Lean_Syntax_isOfKind(v_x_4596_, v___x_4600_);
if (v_foundPanic_4601_ == 0)
{
lean_object* v___x_4602_; 
lean_dec(v_x_4596_);
v___x_4602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4602_;
}
else
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4603_ = lean_unsigned_to_nat(2u);
v___x_4604_ = l_Lean_Syntax_getArg(v_x_4596_, v___x_4603_);
lean_dec(v_x_4596_);
v___x_4605_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4604_, v_a_4597_, v_a_4598_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; uint8_t v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4662_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref(v___x_4605_);
v___x_4607_ = 0;
v___x_4608_ = l_Lean_MessageLog_toList(v_a_4606_);
v___x_4609_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4601_, v___x_4608_, v___x_4607_);
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4662_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4662_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
uint8_t v___x_4614_; 
v___x_4614_ = lean_unbox(v_a_4610_);
lean_dec(v_a_4610_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; lean_object* v_env_4616_; lean_object* v_scopes_4617_; lean_object* v_usedQuotCtxts_4618_; lean_object* v_nextMacroScope_4619_; lean_object* v_maxRecDepth_4620_; lean_object* v_ngen_4621_; lean_object* v_auxDeclNGen_4622_; lean_object* v_infoState_4623_; lean_object* v_traceState_4624_; lean_object* v_snapshotTasks_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4635_; 
lean_del_object(v___x_4612_);
v___x_4615_ = lean_st_ref_take(v_a_4598_);
v_env_4616_ = lean_ctor_get(v___x_4615_, 0);
v_scopes_4617_ = lean_ctor_get(v___x_4615_, 2);
v_usedQuotCtxts_4618_ = lean_ctor_get(v___x_4615_, 3);
v_nextMacroScope_4619_ = lean_ctor_get(v___x_4615_, 4);
v_maxRecDepth_4620_ = lean_ctor_get(v___x_4615_, 5);
v_ngen_4621_ = lean_ctor_get(v___x_4615_, 6);
v_auxDeclNGen_4622_ = lean_ctor_get(v___x_4615_, 7);
v_infoState_4623_ = lean_ctor_get(v___x_4615_, 8);
v_traceState_4624_ = lean_ctor_get(v___x_4615_, 9);
v_snapshotTasks_4625_ = lean_ctor_get(v___x_4615_, 10);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4635_ == 0)
{
lean_object* v_unused_4636_; 
v_unused_4636_ = lean_ctor_get(v___x_4615_, 1);
lean_dec(v_unused_4636_);
v___x_4627_ = v___x_4615_;
v_isShared_4628_ = v_isSharedCheck_4635_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_snapshotTasks_4625_);
lean_inc(v_traceState_4624_);
lean_inc(v_infoState_4623_);
lean_inc(v_auxDeclNGen_4622_);
lean_inc(v_ngen_4621_);
lean_inc(v_maxRecDepth_4620_);
lean_inc(v_nextMacroScope_4619_);
lean_inc(v_usedQuotCtxts_4618_);
lean_inc(v_scopes_4617_);
lean_inc(v_env_4616_);
lean_dec(v___x_4615_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4635_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 1, v_a_4606_);
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_env_4616_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_a_4606_);
lean_ctor_set(v_reuseFailAlloc_4634_, 2, v_scopes_4617_);
lean_ctor_set(v_reuseFailAlloc_4634_, 3, v_usedQuotCtxts_4618_);
lean_ctor_set(v_reuseFailAlloc_4634_, 4, v_nextMacroScope_4619_);
lean_ctor_set(v_reuseFailAlloc_4634_, 5, v_maxRecDepth_4620_);
lean_ctor_set(v_reuseFailAlloc_4634_, 6, v_ngen_4621_);
lean_ctor_set(v_reuseFailAlloc_4634_, 7, v_auxDeclNGen_4622_);
lean_ctor_set(v_reuseFailAlloc_4634_, 8, v_infoState_4623_);
lean_ctor_set(v_reuseFailAlloc_4634_, 9, v_traceState_4624_);
lean_ctor_set(v_reuseFailAlloc_4634_, 10, v_snapshotTasks_4625_);
v___x_4630_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = lean_st_ref_set(v_a_4598_, v___x_4630_);
v___x_4632_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4633_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4632_, v_a_4597_, v_a_4598_);
return v___x_4633_;
}
}
}
else
{
lean_object* v___x_4637_; lean_object* v_env_4638_; lean_object* v_scopes_4639_; lean_object* v_usedQuotCtxts_4640_; lean_object* v_nextMacroScope_4641_; lean_object* v_maxRecDepth_4642_; lean_object* v_ngen_4643_; lean_object* v_auxDeclNGen_4644_; lean_object* v_infoState_4645_; lean_object* v_traceState_4646_; lean_object* v_snapshotTasks_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4660_; 
lean_dec(v_a_4606_);
v___x_4637_ = lean_st_ref_take(v_a_4598_);
v_env_4638_ = lean_ctor_get(v___x_4637_, 0);
v_scopes_4639_ = lean_ctor_get(v___x_4637_, 2);
v_usedQuotCtxts_4640_ = lean_ctor_get(v___x_4637_, 3);
v_nextMacroScope_4641_ = lean_ctor_get(v___x_4637_, 4);
v_maxRecDepth_4642_ = lean_ctor_get(v___x_4637_, 5);
v_ngen_4643_ = lean_ctor_get(v___x_4637_, 6);
v_auxDeclNGen_4644_ = lean_ctor_get(v___x_4637_, 7);
v_infoState_4645_ = lean_ctor_get(v___x_4637_, 8);
v_traceState_4646_ = lean_ctor_get(v___x_4637_, 9);
v_snapshotTasks_4647_ = lean_ctor_get(v___x_4637_, 10);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4660_ == 0)
{
lean_object* v_unused_4661_; 
v_unused_4661_ = lean_ctor_get(v___x_4637_, 1);
lean_dec(v_unused_4661_);
v___x_4649_ = v___x_4637_;
v_isShared_4650_ = v_isSharedCheck_4660_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_snapshotTasks_4647_);
lean_inc(v_traceState_4646_);
lean_inc(v_infoState_4645_);
lean_inc(v_auxDeclNGen_4644_);
lean_inc(v_ngen_4643_);
lean_inc(v_maxRecDepth_4642_);
lean_inc(v_nextMacroScope_4641_);
lean_inc(v_usedQuotCtxts_4640_);
lean_inc(v_scopes_4639_);
lean_inc(v_env_4638_);
lean_dec(v___x_4637_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4660_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4653_; 
v___x_4651_ = l_Lean_MessageLog_empty;
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v___x_4651_);
v___x_4653_ = v___x_4649_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_env_4638_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4659_, 2, v_scopes_4639_);
lean_ctor_set(v_reuseFailAlloc_4659_, 3, v_usedQuotCtxts_4640_);
lean_ctor_set(v_reuseFailAlloc_4659_, 4, v_nextMacroScope_4641_);
lean_ctor_set(v_reuseFailAlloc_4659_, 5, v_maxRecDepth_4642_);
lean_ctor_set(v_reuseFailAlloc_4659_, 6, v_ngen_4643_);
lean_ctor_set(v_reuseFailAlloc_4659_, 7, v_auxDeclNGen_4644_);
lean_ctor_set(v_reuseFailAlloc_4659_, 8, v_infoState_4645_);
lean_ctor_set(v_reuseFailAlloc_4659_, 9, v_traceState_4646_);
lean_ctor_set(v_reuseFailAlloc_4659_, 10, v_snapshotTasks_4647_);
v___x_4653_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4657_; 
v___x_4654_ = lean_st_ref_set(v_a_4598_, v___x_4653_);
v___x_4655_ = lean_box(0);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4655_);
v___x_4657_ = v___x_4612_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
v_a_4663_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4605_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4605_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4676_, lean_object* v_as_4677_, lean_object* v_as_x27_4678_, uint8_t v_b_4679_, lean_object* v_a_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4676_, v_as_x27_4678_, v_b_4679_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4685_, lean_object* v_as_4686_, lean_object* v_as_x27_4687_, lean_object* v_b_4688_, lean_object* v_a_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
uint8_t v_foundPanic_boxed_4693_; uint8_t v_b_boxed_4694_; lean_object* v_res_4695_; 
v_foundPanic_boxed_4693_ = lean_unbox(v_foundPanic_4685_);
v_b_boxed_4694_ = lean_unbox(v_b_4688_);
v_res_4695_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4693_, v_as_4686_, v_as_x27_4687_, v_b_boxed_4694_, v_a_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v_as_4686_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4704_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4705_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4706_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4707_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4708_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4704_, v___x_4705_, v___x_4706_, v___x_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4710_;
}
}
lean_object* runtime_initialize_Lean_Elab_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_CodeActions_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_GuardMsgs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_guard__msgs_diff = lean_io_result_get_value(res);
lean_mark_persistent(l_guard__msgs_diff);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_GuardMsgs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Notation(uint8_t builtin);
lean_object* initialize_Lean_Server_CodeActions_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_GuardMsgs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_GuardMsgs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_GuardMsgs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_GuardMsgs(builtin);
}
#ifdef __cplusplus
}
#endif
