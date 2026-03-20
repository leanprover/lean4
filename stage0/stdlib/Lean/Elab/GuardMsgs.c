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
lean_object* v___y_89_; lean_object* v___y_93_; uint8_t v___y_94_; uint8_t v___y_96_; lean_object* v___y_97_; uint32_t v___y_98_; lean_object* v_str_102_; lean_object* v_pos_114_; lean_object* v_endPos_115_; uint8_t v_severity_116_; lean_object* v_caption_117_; lean_object* v_data_118_; lean_object* v___x_119_; lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v_str_134_; lean_object* v_str_146_; lean_object* v___y_157_; lean_object* v_str_161_; lean_object* v___x_168_; uint8_t v___x_169_; 
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
v___y_89_ = v___y_97_;
goto v___jp_88_;
}
else
{
v___y_93_ = v___y_97_;
v___y_94_ = v___y_96_;
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
v___y_96_ = v___x_105_;
v___y_97_ = v_str_102_;
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
v___y_96_ = v___x_105_;
v___y_97_ = v_str_102_;
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
v___y_96_ = v___x_105_;
v___y_97_ = v_str_102_;
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
uint8_t v___x_2161__boxed_445_; uint8_t v_res_446_; lean_object* v_r_447_; 
v___x_2161__boxed_445_ = lean_unbox(v___x_443_);
v_res_446_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_2161__boxed_445_, v_x_444_);
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
uint8_t v___x_2167__boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v___x_2167__boxed_456_ = lean_unbox(v___x_454_);
v_res_457_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_2167__boxed_456_, v_msg_455_);
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
uint8_t v___x_2176__boxed_467_; uint8_t v_res_468_; lean_object* v_r_469_; 
v___x_2176__boxed_467_ = lean_unbox(v___x_465_);
v_res_468_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_2176__boxed_467_, v_msg_466_);
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
uint8_t v___x_2185__boxed_478_; uint8_t v_res_479_; lean_object* v_r_480_; 
v___x_2185__boxed_478_ = lean_unbox(v___x_476_);
v_res_479_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_2185__boxed_478_, v_msg_477_);
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
uint8_t v_a_14073__boxed_580_; uint8_t v_res_581_; lean_object* v_r_582_; 
v_a_14073__boxed_580_ = lean_unbox(v_a_578_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_576_, v_snd_577_, v_a_14073__boxed_580_, v___y_579_);
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
uint8_t v___x_14948__boxed_1040_; size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; lean_object* v_res_1043_; 
v___x_14948__boxed_1040_ = lean_unbox(v___x_1035_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1038_);
lean_dec(v_stop_1038_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_14948__boxed_1040_, v_as_1036_, v_i_boxed_1041_, v_stop_boxed_1042_, v_b_1039_);
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
v___x_1245_ = lean_nat_dec_lt(v_basePos_1240_, v___x_1243_);
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
lean_object* v_fileName_1698_; lean_object* v_fileMap_1699_; lean_object* v_currRecDepth_1700_; lean_object* v_cmdPos_1701_; lean_object* v_macroStack_1702_; lean_object* v_quotContext_x3f_1703_; lean_object* v_currMacroScope_1704_; lean_object* v_ref_1705_; lean_object* v_cancelTk_x3f_1706_; uint8_t v_suppressElabErrors_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1771_; 
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
v_isSharedCheck_1771_ = !lean_is_exclusive(v_a_1695_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v_a_1695_, 8);
lean_dec(v_unused_1772_);
v___x_1709_ = v_a_1695_;
v_isShared_1710_ = v_isSharedCheck_1771_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_cancelTk_x3f_1706_);
lean_inc(v_ref_1705_);
lean_inc(v_currMacroScope_1704_);
lean_inc(v_quotContext_x3f_1703_);
lean_inc(v_macroStack_1702_);
lean_inc(v_cmdPos_1701_);
lean_inc(v_currRecDepth_1700_);
lean_inc(v_fileMap_1699_);
lean_inc(v_fileName_1698_);
lean_dec(v_a_1695_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1771_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = lean_box(0);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 8, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fileName_1698_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_fileMap_1699_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_currRecDepth_1700_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_cmdPos_1701_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_macroStack_1702_);
lean_ctor_set(v_reuseFailAlloc_1770_, 5, v_quotContext_x3f_1703_);
lean_ctor_set(v_reuseFailAlloc_1770_, 6, v_currMacroScope_1704_);
lean_ctor_set(v_reuseFailAlloc_1770_, 7, v_ref_1705_);
lean_ctor_set(v_reuseFailAlloc_1770_, 8, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1770_, 9, v_cancelTk_x3f_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*10, v_suppressElabErrors_1707_);
v___x_1713_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; 
lean_inc(v_a_1696_);
v___x_1714_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1694_, v___x_1713_, v_a_1696_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1760_; 
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1761_);
v___x_1716_ = v___x_1714_;
v_isShared_1717_ = v_isSharedCheck_1760_;
goto v_resetjp_1715_;
}
else
{
lean_dec(v___x_1714_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1760_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_messages_1720_; lean_object* v___y_1722_; lean_object* v_snapshotTasks_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1718_ = lean_st_ref_get(v_a_1696_);
v___x_1719_ = lean_st_ref_get(v_a_1696_);
v_messages_1720_ = lean_ctor_get(v___x_1718_, 1);
lean_inc_ref(v_messages_1720_);
lean_dec(v___x_1718_);
v_snapshotTasks_1748_ = lean_ctor_get(v___x_1719_, 10);
lean_inc_ref(v_snapshotTasks_1748_);
lean_dec(v___x_1719_);
v___x_1749_ = l_Lean_MessageLog_empty;
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_array_get_size(v_snapshotTasks_1748_);
v___x_1752_ = lean_nat_dec_lt(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v_snapshotTasks_1748_);
v___y_1722_ = v___x_1749_;
goto v___jp_1721_;
}
else
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_le(v___x_1751_, v___x_1751_);
if (v___x_1753_ == 0)
{
if (v___x_1752_ == 0)
{
lean_dec_ref(v_snapshotTasks_1748_);
v___y_1722_ = v___x_1749_;
goto v___jp_1721_;
}
else
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = lean_usize_of_nat(v___x_1751_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1748_, v___x_1754_, v___x_1755_, v___x_1749_);
lean_dec_ref(v_snapshotTasks_1748_);
v___y_1722_ = v___x_1756_;
goto v___jp_1721_;
}
}
else
{
size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = lean_usize_of_nat(v___x_1751_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1748_, v___x_1757_, v___x_1758_, v___x_1749_);
lean_dec_ref(v_snapshotTasks_1748_);
v___y_1722_ = v___x_1759_;
goto v___jp_1721_;
}
}
v___jp_1721_:
{
lean_object* v___x_1723_; lean_object* v_env_1724_; lean_object* v_messages_1725_; lean_object* v_scopes_1726_; lean_object* v_usedQuotCtxts_1727_; lean_object* v_nextMacroScope_1728_; lean_object* v_maxRecDepth_1729_; lean_object* v_ngen_1730_; lean_object* v_auxDeclNGen_1731_; lean_object* v_infoState_1732_; lean_object* v_traceState_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1746_; 
v___x_1723_ = lean_st_ref_take(v_a_1696_);
v_env_1724_ = lean_ctor_get(v___x_1723_, 0);
v_messages_1725_ = lean_ctor_get(v___x_1723_, 1);
v_scopes_1726_ = lean_ctor_get(v___x_1723_, 2);
v_usedQuotCtxts_1727_ = lean_ctor_get(v___x_1723_, 3);
v_nextMacroScope_1728_ = lean_ctor_get(v___x_1723_, 4);
v_maxRecDepth_1729_ = lean_ctor_get(v___x_1723_, 5);
v_ngen_1730_ = lean_ctor_get(v___x_1723_, 6);
v_auxDeclNGen_1731_ = lean_ctor_get(v___x_1723_, 7);
v_infoState_1732_ = lean_ctor_get(v___x_1723_, 8);
v_traceState_1733_ = lean_ctor_get(v___x_1723_, 9);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1723_, 10);
lean_dec(v_unused_1747_);
v___x_1735_ = v___x_1723_;
v_isShared_1736_ = v_isSharedCheck_1746_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_traceState_1733_);
lean_inc(v_infoState_1732_);
lean_inc(v_auxDeclNGen_1731_);
lean_inc(v_ngen_1730_);
lean_inc(v_maxRecDepth_1729_);
lean_inc(v_nextMacroScope_1728_);
lean_inc(v_usedQuotCtxts_1727_);
lean_inc(v_scopes_1726_);
lean_inc(v_messages_1725_);
lean_inc(v_env_1724_);
lean_dec(v___x_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1746_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 10, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_env_1724_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_messages_1725_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_scopes_1726_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_usedQuotCtxts_1727_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_nextMacroScope_1728_);
lean_ctor_set(v_reuseFailAlloc_1745_, 5, v_maxRecDepth_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 6, v_ngen_1730_);
lean_ctor_set(v_reuseFailAlloc_1745_, 7, v_auxDeclNGen_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 8, v_infoState_1732_);
lean_ctor_set(v_reuseFailAlloc_1745_, 9, v_traceState_1733_);
lean_ctor_set(v_reuseFailAlloc_1745_, 10, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1740_ = lean_st_ref_set(v_a_1696_, v___x_1739_);
lean_dec(v_a_1696_);
v___x_1741_ = l_Lean_MessageLog_append(v_messages_1720_, v___y_1722_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1741_);
v___x_1743_ = v___x_1716_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
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
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1696_);
v_a_1762_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1714_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1714_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1773_, v_a_1774_, v_a_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1778_, lean_object* v_opt_1779_){
_start:
{
lean_object* v_name_1780_; lean_object* v_defValue_1781_; lean_object* v_map_1782_; lean_object* v___x_1783_; 
v_name_1780_ = lean_ctor_get(v_opt_1779_, 0);
v_defValue_1781_ = lean_ctor_get(v_opt_1779_, 1);
v_map_1782_ = lean_ctor_get(v_opts_1778_, 0);
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1782_, v_name_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_unbox(v_defValue_1781_);
return v___x_1784_;
}
else
{
lean_object* v_val_1785_; 
v_val_1785_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_val_1785_);
lean_dec_ref(v___x_1783_);
if (lean_obj_tag(v_val_1785_) == 1)
{
uint8_t v_v_1786_; 
v_v_1786_ = lean_ctor_get_uint8(v_val_1785_, 0);
lean_dec_ref(v_val_1785_);
return v_v_1786_;
}
else
{
uint8_t v___x_1787_; 
lean_dec(v_val_1785_);
v___x_1787_ = lean_unbox(v_defValue_1781_);
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1788_, lean_object* v_opt_1789_){
_start:
{
uint8_t v_res_1790_; lean_object* v_r_1791_; 
v_res_1790_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1788_, v_opt_1789_);
lean_dec_ref(v_opt_1789_);
lean_dec_ref(v_opts_1788_);
v_r_1791_ = lean_box(v_res_1790_);
return v_r_1791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1796_);
lean_dec_ref(v_s_1796_);
return v_res_1797_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_box(1);
v___x_1799_ = l_Lean_MessageData_ofFormat(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1804_ = l_Lean_MessageData_ofFormat(v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1806_) == 0)
{
return v_x_1805_;
}
else
{
lean_object* v_head_1807_; lean_object* v_tail_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1830_; 
v_head_1807_ = lean_ctor_get(v_x_1806_, 0);
v_tail_1808_ = lean_ctor_get(v_x_1806_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_x_1806_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1810_ = v_x_1806_;
v_isShared_1811_ = v_isSharedCheck_1830_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_tail_1808_);
lean_inc(v_head_1807_);
lean_dec(v_x_1806_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1830_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_before_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1828_; 
v_before_1812_ = lean_ctor_get(v_head_1807_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_head_1807_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_head_1807_, 1);
lean_dec(v_unused_1829_);
v___x_1814_ = v_head_1807_;
v_isShared_1815_ = v_isSharedCheck_1828_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_before_1812_);
lean_dec(v_head_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1828_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 7);
lean_ctor_set(v___x_1814_, 1, v___x_1816_);
lean_ctor_set(v___x_1814_, 0, v_x_1805_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_x_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 7);
lean_ctor_set(v___x_1810_, 1, v___x_1819_);
lean_ctor_set(v___x_1810_, 0, v___x_1818_);
v___x_1821_ = v___x_1810_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_MessageData_ofSyntax(v_before_1812_);
v___x_1823_ = l_Lean_indentD(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1821_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v_x_1805_ = v___x_1824_;
v_x_1806_ = v_tail_1808_;
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
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1835_ = l_Lean_MessageData_ofFormat(v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1836_, lean_object* v_macroStack_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v_scopes_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_opts_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1840_ = lean_st_ref_get(v___y_1838_);
v_scopes_1841_ = lean_ctor_get(v___x_1840_, 2);
lean_inc(v_scopes_1841_);
lean_dec(v___x_1840_);
v___x_1842_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1843_ = l_List_head_x21___redArg(v___x_1842_, v_scopes_1841_);
lean_dec(v_scopes_1841_);
v_opts_1844_ = lean_ctor_get(v___x_1843_, 1);
lean_inc_ref(v_opts_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = l_Lean_Elab_pp_macroStack;
v___x_1846_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1844_, v___x_1845_);
lean_dec_ref(v_opts_1844_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_dec(v_macroStack_1837_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_msgData_1836_);
return v___x_1847_;
}
else
{
if (lean_obj_tag(v_macroStack_1837_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_msgData_1836_);
return v___x_1848_;
}
else
{
lean_object* v_head_1849_; lean_object* v_after_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1865_; 
v_head_1849_ = lean_ctor_get(v_macroStack_1837_, 0);
lean_inc(v_head_1849_);
v_after_1850_ = lean_ctor_get(v_head_1849_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_head_1849_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v_head_1849_, 0);
lean_dec(v_unused_1866_);
v___x_1852_ = v_head_1849_;
v_isShared_1853_ = v_isSharedCheck_1865_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_after_1850_);
lean_dec(v_head_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1865_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 7);
lean_ctor_set(v___x_1852_, 1, v___x_1854_);
lean_ctor_set(v___x_1852_, 0, v_msgData_1836_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_msgData_1836_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_msgData_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1857_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_MessageData_ofSyntax(v_after_1850_);
v___x_1860_ = l_Lean_indentD(v___x_1859_);
v_msgData_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1861_, 0, v___x_1858_);
lean_ctor_set(v_msgData_1861_, 1, v___x_1860_);
v___x_1862_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1861_, v_macroStack_1837_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1867_, lean_object* v_macroStack_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1867_, v_macroStack_1868_, v___y_1869_);
lean_dec(v___y_1869_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
lean_ctor_set(v___x_1877_, 2, v___x_1876_);
lean_ctor_set(v___x_1877_, 3, v___x_1875_);
lean_ctor_set(v___x_1877_, 4, v___x_1875_);
lean_ctor_set(v___x_1877_, 5, v___x_1875_);
lean_ctor_set(v___x_1877_, 6, v___x_1875_);
lean_ctor_set(v___x_1877_, 7, v___x_1875_);
lean_ctor_set(v___x_1877_, 8, v___x_1875_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = lean_unsigned_to_nat(32u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1881_ = ((size_t)5ULL);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_unsigned_to_nat(32u);
v___x_1884_ = lean_mk_empty_array_with_capacity(v___x_1883_);
v___x_1885_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1886_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1884_);
lean_ctor_set(v___x_1886_, 2, v___x_1882_);
lean_ctor_set(v___x_1886_, 3, v___x_1882_);
lean_ctor_set_usize(v___x_1886_, 4, v___x_1881_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = lean_box(1);
v___x_1888_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1889_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1888_);
lean_ctor_set(v___x_1890_, 2, v___x_1887_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v_env_1895_; lean_object* v___x_1896_; lean_object* v_scopes_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_opts_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1894_ = lean_st_ref_get(v___y_1892_);
v_env_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_ref(v_env_1895_);
lean_dec(v___x_1894_);
v___x_1896_ = lean_st_ref_get(v___y_1892_);
v_scopes_1897_ = lean_ctor_get(v___x_1896_, 2);
lean_inc(v_scopes_1897_);
lean_dec(v___x_1896_);
v___x_1898_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1899_ = l_List_head_x21___redArg(v___x_1898_, v_scopes_1897_);
lean_dec(v_scopes_1897_);
v_opts_1900_ = lean_ctor_get(v___x_1899_, 1);
lean_inc_ref(v_opts_1900_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1902_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1903_, 0, v_env_1895_);
lean_ctor_set(v___x_1903_, 1, v___x_1901_);
lean_ctor_set(v___x_1903_, 2, v___x_1902_);
lean_ctor_set(v___x_1903_, 3, v_opts_1900_);
v___x_1904_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v_msgData_1891_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1906_, v___y_1907_);
lean_dec(v___y_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Elab_Command_getRef___redArg(v___y_1911_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_macroStack_1916_; lean_object* v___x_1917_; lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
v_macroStack_1916_ = lean_ctor_get(v___y_1911_, 4);
lean_inc(v_macroStack_1916_);
lean_dec_ref(v___y_1911_);
v___x_1917_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1910_, v___y_1912_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
lean_inc(v_macroStack_1916_);
v___x_1919_ = l_Lean_Elab_getBetterRef(v_a_1915_, v_macroStack_1916_);
lean_dec(v_a_1915_);
v___x_1920_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1918_, v_macroStack_1916_, v___y_1912_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1919_);
lean_ctor_set(v___x_1925_, 1, v_a_1921_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 1);
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_msg_1910_);
v_a_1930_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1914_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1914_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1943_, lean_object* v_msg_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Elab_Command_getRef___redArg(v___y_1945_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v_fileName_1950_; lean_object* v_fileMap_1951_; lean_object* v_currRecDepth_1952_; lean_object* v_cmdPos_1953_; lean_object* v_macroStack_1954_; lean_object* v_quotContext_x3f_1955_; lean_object* v_currMacroScope_1956_; lean_object* v_snap_x3f_1957_; lean_object* v_cancelTk_x3f_1958_; uint8_t v_suppressElabErrors_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1968_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
v_fileName_1950_ = lean_ctor_get(v___y_1945_, 0);
v_fileMap_1951_ = lean_ctor_get(v___y_1945_, 1);
v_currRecDepth_1952_ = lean_ctor_get(v___y_1945_, 2);
v_cmdPos_1953_ = lean_ctor_get(v___y_1945_, 3);
v_macroStack_1954_ = lean_ctor_get(v___y_1945_, 4);
v_quotContext_x3f_1955_ = lean_ctor_get(v___y_1945_, 5);
v_currMacroScope_1956_ = lean_ctor_get(v___y_1945_, 6);
v_snap_x3f_1957_ = lean_ctor_get(v___y_1945_, 8);
v_cancelTk_x3f_1958_ = lean_ctor_get(v___y_1945_, 9);
v_suppressElabErrors_1959_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*10);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___y_1945_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v___y_1945_, 7);
lean_dec(v_unused_1969_);
v___x_1961_ = v___y_1945_;
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_cancelTk_x3f_1958_);
lean_inc(v_snap_x3f_1957_);
lean_inc(v_currMacroScope_1956_);
lean_inc(v_quotContext_x3f_1955_);
lean_inc(v_macroStack_1954_);
lean_inc(v_cmdPos_1953_);
lean_inc(v_currRecDepth_1952_);
lean_inc(v_fileMap_1951_);
lean_inc(v_fileName_1950_);
lean_dec(v___y_1945_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_ref_1963_; lean_object* v___x_1965_; 
v_ref_1963_ = l_Lean_replaceRef(v_ref_1943_, v_a_1949_);
lean_dec(v_a_1949_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 7, v_ref_1963_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_fileName_1950_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_fileMap_1951_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_currRecDepth_1952_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_cmdPos_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_macroStack_1954_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v_quotContext_x3f_1955_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_currMacroScope_1956_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_ref_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_snap_x3f_1957_);
lean_ctor_set(v_reuseFailAlloc_1967_, 9, v_cancelTk_x3f_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1967_, sizeof(void*)*10, v_suppressElabErrors_1959_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1944_, v___x_1965_, v___y_1946_);
return v___x_1966_;
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v___y_1945_);
lean_dec_ref(v_msg_1944_);
v_a_1970_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1948_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1948_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_1978_, lean_object* v_msg_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_1978_, v_msg_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec(v_ref_1978_);
return v_res_1983_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_1986_ = l_Lean_stringToMessageData(v___x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_val_2001_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_unsigned_to_nat(1u);
v___x_2009_ = l_Lean_Syntax_getArg(v_stx_1990_, v___x_2008_);
switch(lean_obj_tag(v___x_2009_))
{
case 2:
{
lean_object* v_val_2010_; 
lean_dec_ref(v___y_1991_);
lean_dec(v_stx_1990_);
v_val_2010_ = lean_ctor_get(v___x_2009_, 1);
lean_inc_ref(v_val_2010_);
lean_dec_ref(v___x_2009_);
v_val_2001_ = v_val_2010_;
goto v___jp_2000_;
}
case 1:
{
lean_object* v_kind_2011_; 
v_kind_2011_ = lean_ctor_get(v___x_2009_, 1);
lean_inc(v_kind_2011_);
if (lean_obj_tag(v_kind_2011_) == 1)
{
lean_object* v_pre_2012_; 
v_pre_2012_ = lean_ctor_get(v_kind_2011_, 0);
lean_inc(v_pre_2012_);
if (lean_obj_tag(v_pre_2012_) == 1)
{
lean_object* v_pre_2013_; 
v_pre_2013_ = lean_ctor_get(v_pre_2012_, 0);
lean_inc(v_pre_2013_);
if (lean_obj_tag(v_pre_2013_) == 1)
{
lean_object* v_pre_2014_; 
v_pre_2014_ = lean_ctor_get(v_pre_2013_, 0);
lean_inc(v_pre_2014_);
if (lean_obj_tag(v_pre_2014_) == 1)
{
lean_object* v_pre_2015_; 
v_pre_2015_ = lean_ctor_get(v_pre_2014_, 0);
if (lean_obj_tag(v_pre_2015_) == 0)
{
lean_object* v_str_2016_; lean_object* v_str_2017_; lean_object* v_str_2018_; lean_object* v_str_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v_str_2016_ = lean_ctor_get(v_kind_2011_, 1);
lean_inc_ref(v_str_2016_);
lean_dec_ref(v_kind_2011_);
v_str_2017_ = lean_ctor_get(v_pre_2012_, 1);
lean_inc_ref(v_str_2017_);
lean_dec_ref(v_pre_2012_);
v_str_2018_ = lean_ctor_get(v_pre_2013_, 1);
lean_inc_ref(v_str_2018_);
lean_dec_ref(v_pre_2013_);
v_str_2019_ = lean_ctor_get(v_pre_2014_, 1);
lean_inc_ref(v_str_2019_);
lean_dec_ref(v_pre_2014_);
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0));
v___x_2021_ = lean_string_dec_eq(v_str_2019_, v___x_2020_);
lean_dec_ref(v_str_2019_);
if (v___x_2021_ == 0)
{
lean_dec_ref(v_str_2018_);
lean_dec_ref(v_str_2017_);
lean_dec_ref(v_str_2016_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
else
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2023_ = lean_string_dec_eq(v_str_2018_, v___x_2022_);
lean_dec_ref(v_str_2018_);
if (v___x_2023_ == 0)
{
lean_dec_ref(v_str_2017_);
lean_dec_ref(v_str_2016_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
else
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2025_ = lean_string_dec_eq(v_str_2017_, v___x_2024_);
lean_dec_ref(v_str_2017_);
if (v___x_2025_ == 0)
{
lean_dec_ref(v_str_2016_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2027_ = lean_string_dec_eq(v_str_2016_, v___x_2026_);
lean_dec_ref(v_str_2016_);
if (v___x_2027_ == 0)
{
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_2028_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v___x_2029_) == 2)
{
lean_object* v_val_2030_; 
lean_dec_ref(v___y_1991_);
lean_dec(v_stx_1990_);
v_val_2030_ = lean_ctor_get(v___x_2029_, 1);
lean_inc_ref(v_val_2030_);
lean_dec_ref(v___x_2029_);
v_val_2001_ = v_val_2030_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v___x_2029_);
v___x_2031_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1990_);
v___x_2032_ = l_Lean_MessageData_ofSyntax(v_stx_1990_);
v___x_2033_ = l_Lean_indentD(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2031_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1990_, v___x_2034_, v___y_1991_, v___y_1992_);
lean_dec(v_stx_1990_);
return v___x_2035_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2014_);
lean_dec_ref(v_pre_2013_);
lean_dec_ref(v_pre_2012_);
lean_dec_ref(v_kind_2011_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
}
else
{
lean_dec_ref(v_pre_2013_);
lean_dec(v_pre_2014_);
lean_dec_ref(v_pre_2012_);
lean_dec_ref(v_kind_2011_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
}
else
{
lean_dec(v_pre_2013_);
lean_dec_ref(v_pre_2012_);
lean_dec_ref(v_kind_2011_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
}
else
{
lean_dec(v_pre_2012_);
lean_dec_ref(v_kind_2011_);
lean_dec_ref(v___x_2009_);
goto v___jp_1994_;
}
}
else
{
lean_dec_ref(v___x_2009_);
lean_dec(v_kind_2011_);
goto v___jp_1994_;
}
}
default: 
{
lean_dec(v___x_2009_);
goto v___jp_1994_;
}
}
v___jp_1994_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1995_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1990_);
v___x_1996_ = l_Lean_MessageData_ofSyntax(v_stx_1990_);
v___x_1997_ = l_Lean_indentD(v___x_1996_);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1995_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1990_, v___x_1998_, v___y_1991_, v___y_1992_);
lean_dec(v_stx_1990_);
return v___x_1999_;
}
v___jp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = lean_string_utf8_byte_size(v_val_2001_);
v___x_2004_ = lean_unsigned_to_nat(2u);
v___x_2005_ = lean_nat_sub(v___x_2003_, v___x_2004_);
v___x_2006_ = lean_string_utf8_extract(v_val_2001_, v___x_2002_, v___x_2005_);
lean_dec(v___x_2005_);
lean_dec_ref(v_val_2001_);
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_b_2044_){
_start:
{
lean_object* v_a_2046_; uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2050_ == 0)
{
return v_b_2044_;
}
else
{
lean_object* v_a_2051_; lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v_out_2054_; uint8_t v___x_2055_; 
v_a_2051_ = lean_array_uget_borrowed(v_as_2041_, v_i_2043_);
v_fst_2052_ = lean_ctor_get(v_a_2051_, 0);
v_snd_2053_ = lean_ctor_get(v_a_2051_, 1);
v_out_2054_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2055_ = lean_string_dec_eq(v_snd_2053_, v_out_2054_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2056_ = lean_unbox(v_fst_2052_);
v___x_2057_ = l_Lean_Diff_Action_linePrefix(v___x_2056_);
v___x_2058_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2059_ = lean_string_append(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_string_append(v___x_2059_, v_snd_2053_);
v___x_2061_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2062_ = lean_string_append(v___x_2060_, v___x_2061_);
v___x_2063_ = lean_string_append(v_b_2044_, v___x_2062_);
lean_dec_ref(v___x_2062_);
v_a_2046_ = v___x_2063_;
goto v___jp_2045_;
}
else
{
uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2064_ = lean_unbox(v_fst_2052_);
v___x_2065_ = l_Lean_Diff_Action_linePrefix(v___x_2064_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2067_ = lean_string_append(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_string_append(v_b_2044_, v___x_2067_);
lean_dec_ref(v___x_2067_);
v_a_2046_ = v___x_2068_;
goto v___jp_2045_;
}
}
v___jp_2045_:
{
size_t v___x_2047_; size_t v___x_2048_; 
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2043_, v___x_2047_);
v_i_2043_ = v___x_2048_;
v_b_2044_ = v_a_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2069_, lean_object* v_sz_2070_, lean_object* v_i_2071_, lean_object* v_b_2072_){
_start:
{
size_t v_sz_boxed_2073_; size_t v_i_boxed_2074_; lean_object* v_res_2075_; 
v_sz_boxed_2073_ = lean_unbox_usize(v_sz_2070_);
lean_dec(v_sz_2070_);
v_i_boxed_2074_ = lean_unbox_usize(v_i_2071_);
lean_dec(v_i_2071_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2069_, v_sz_boxed_2073_, v_i_boxed_2074_, v_b_2072_);
lean_dec_ref(v_as_2069_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2076_){
_start:
{
lean_object* v_out_2077_; size_t v_sz_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v_out_2077_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2078_ = lean_array_size(v_lines_2076_);
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2076_, v_sz_2078_, v___x_2079_, v_out_2077_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2081_);
lean_dec_ref(v_lines_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2083_, lean_object* v_as_x27_2084_, lean_object* v_b_2085_){
_start:
{
if (lean_obj_tag(v_as_x27_2084_) == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref(v_filterFn_2083_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_b_2085_);
return v___x_2087_;
}
else
{
lean_object* v_head_2088_; uint8_t v_isSilent_2089_; 
v_head_2088_ = lean_ctor_get(v_as_x27_2084_, 0);
v_isSilent_2089_ = lean_ctor_get_uint8(v_head_2088_, sizeof(void*)*5 + 2);
if (v_isSilent_2089_ == 0)
{
lean_object* v_tail_2090_; lean_object* v_fst_2091_; lean_object* v_snd_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2112_; 
lean_inc(v_head_2088_);
v_tail_2090_ = lean_ctor_get(v_as_x27_2084_, 1);
lean_inc(v_tail_2090_);
lean_dec_ref(v_as_x27_2084_);
v_fst_2091_ = lean_ctor_get(v_b_2085_, 0);
v_snd_2092_ = lean_ctor_get(v_b_2085_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2094_ = v_b_2085_;
v_isShared_2095_ = v_isSharedCheck_2112_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_snd_2092_);
lean_inc(v_fst_2091_);
lean_dec(v_b_2085_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2112_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
lean_inc_ref(v_filterFn_2083_);
lean_inc(v_head_2088_);
v___x_2096_ = lean_apply_1(v_filterFn_2083_, v_head_2088_);
v___x_2097_ = lean_unbox(v___x_2096_);
switch(v___x_2097_)
{
case 0:
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = l_Lean_MessageLog_add(v_head_2088_, v_fst_2091_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2098_);
v___x_2100_ = v___x_2094_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_snd_2092_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
v_as_x27_2084_ = v_tail_2090_;
v_b_2085_ = v___x_2100_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2104_; 
lean_dec(v_head_2088_);
if (v_isShared_2095_ == 0)
{
v___x_2104_ = v___x_2094_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_fst_2091_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_snd_2092_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v_as_x27_2084_ = v_tail_2090_;
v_b_2085_ = v___x_2104_;
goto _start;
}
}
default: 
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = l_Lean_MessageLog_add(v_head_2088_, v_snd_2092_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v___x_2107_);
v___x_2109_ = v___x_2094_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_fst_2091_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
v_as_x27_2084_ = v_tail_2090_;
v_b_2085_ = v___x_2109_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2113_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_tail_2113_ = lean_ctor_get(v_as_x27_2084_, 1);
lean_inc(v_tail_2113_);
lean_dec_ref(v_as_x27_2084_);
v_fst_2114_ = lean_ctor_get(v_b_2085_, 0);
v_snd_2115_ = lean_ctor_get(v_b_2085_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v_b_2085_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snd_2115_);
lean_inc(v_fst_2114_);
lean_dec(v_b_2085_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_fst_2114_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_snd_2115_);
v___x_2120_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
v_as_x27_2084_ = v_tail_2113_;
v_b_2085_ = v___x_2120_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2124_, lean_object* v_as_x27_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2124_, v_as_x27_2125_, v_b_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2129_, lean_object* v_a_2130_, uint8_t v_b_2131_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = 0;
switch(lean_obj_tag(v_a_2130_))
{
case 0:
{
uint8_t v___x_2133_; 
lean_dec_ref(v_a_2130_);
v___x_2133_ = 1;
return v___x_2133_;
}
case 1:
{
lean_object* v_pos_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2147_; 
v_pos_2134_ = lean_ctor_get(v_a_2130_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_2130_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2136_ = v_a_2130_;
v_isShared_2137_ = v_isSharedCheck_2147_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_pos_2134_);
lean_dec(v_a_2130_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2147_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_str_2138_; lean_object* v_startInclusive_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v_str_2138_ = lean_ctor_get(v_s_2129_, 0);
v_startInclusive_2139_ = lean_ctor_get(v_s_2129_, 1);
v___x_2140_ = lean_nat_add(v_startInclusive_2139_, v_pos_2134_);
lean_dec(v_pos_2134_);
v___x_2141_ = lean_string_utf8_next_fast(v_str_2138_, v___x_2140_);
lean_dec(v___x_2140_);
v___x_2142_ = lean_nat_sub(v___x_2141_, v_startInclusive_2139_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2142_);
v___x_2144_ = v___x_2136_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_a_2130_ = v___x_2144_;
v_b_2131_ = v___x_2132_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2148_; lean_object* v_table_2149_; lean_object* v_stackPos_2150_; lean_object* v_needlePos_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2204_; 
v_needle_2148_ = lean_ctor_get(v_a_2130_, 0);
v_table_2149_ = lean_ctor_get(v_a_2130_, 1);
v_stackPos_2150_ = lean_ctor_get(v_a_2130_, 2);
v_needlePos_2151_ = lean_ctor_get(v_a_2130_, 3);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_a_2130_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2153_ = v_a_2130_;
v_isShared_2154_ = v_isSharedCheck_2204_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_needlePos_2151_);
lean_inc(v_stackPos_2150_);
lean_inc(v_table_2149_);
lean_inc(v_needle_2148_);
lean_dec(v_a_2130_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2204_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_str_2155_; lean_object* v_startInclusive_2156_; lean_object* v_endExclusive_2157_; lean_object* v_str_2158_; lean_object* v_startInclusive_2159_; lean_object* v_endExclusive_2160_; lean_object* v_basePos_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v_str_2155_ = lean_ctor_get(v_needle_2148_, 0);
v_startInclusive_2156_ = lean_ctor_get(v_needle_2148_, 1);
v_endExclusive_2157_ = lean_ctor_get(v_needle_2148_, 2);
v_str_2158_ = lean_ctor_get(v_s_2129_, 0);
v_startInclusive_2159_ = lean_ctor_get(v_s_2129_, 1);
v_endExclusive_2160_ = lean_ctor_get(v_s_2129_, 2);
v_basePos_2161_ = lean_nat_sub(v_stackPos_2150_, v_needlePos_2151_);
v___x_2162_ = lean_nat_sub(v_endExclusive_2157_, v_startInclusive_2156_);
v___x_2163_ = lean_nat_add(v_basePos_2161_, v___x_2162_);
v___x_2164_ = lean_nat_sub(v_endExclusive_2160_, v_startInclusive_2159_);
v___x_2165_ = lean_nat_dec_le(v___x_2163_, v___x_2164_);
lean_dec(v___x_2163_);
if (v___x_2165_ == 0)
{
uint8_t v___x_2166_; 
lean_dec(v___x_2162_);
lean_del_object(v___x_2153_);
lean_dec(v_needlePos_2151_);
lean_dec(v_stackPos_2150_);
lean_dec_ref(v_table_2149_);
lean_dec_ref(v_needle_2148_);
v___x_2166_ = lean_nat_dec_lt(v_basePos_2161_, v___x_2164_);
lean_dec(v___x_2164_);
lean_dec(v_basePos_2161_);
if (v___x_2166_ == 0)
{
return v_b_2131_;
}
else
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_box(3);
v_a_2130_ = v___x_2167_;
v_b_2131_ = v___x_2132_;
goto _start;
}
}
else
{
lean_object* v___x_2169_; uint8_t v_stackByte_2170_; lean_object* v___x_2171_; uint8_t v_patByte_2172_; uint8_t v___x_2173_; 
lean_dec(v___x_2164_);
lean_dec(v_basePos_2161_);
v___x_2169_ = lean_nat_add(v_startInclusive_2159_, v_stackPos_2150_);
v_stackByte_2170_ = lean_string_get_byte_fast(v_str_2158_, v___x_2169_);
v___x_2171_ = lean_nat_add(v_startInclusive_2156_, v_needlePos_2151_);
v_patByte_2172_ = lean_string_get_byte_fast(v_str_2155_, v___x_2171_);
v___x_2173_ = lean_uint8_dec_eq(v_stackByte_2170_, v_patByte_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
lean_dec(v___x_2162_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_nat_dec_eq(v_needlePos_2151_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v_newNeedlePos_2178_; uint8_t v___x_2179_; 
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_sub(v_needlePos_2151_, v___x_2176_);
lean_dec(v_needlePos_2151_);
v_newNeedlePos_2178_ = lean_array_fget_borrowed(v_table_2149_, v___x_2177_);
lean_dec(v___x_2177_);
v___x_2179_ = lean_nat_dec_eq(v_newNeedlePos_2178_, v___x_2174_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2181_; 
lean_inc(v_newNeedlePos_2178_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 3, v_newNeedlePos_2178_);
v___x_2181_ = v___x_2153_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_needle_2148_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_table_2149_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_stackPos_2150_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_newNeedlePos_2178_);
v___x_2181_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
v_a_2130_ = v___x_2181_;
v_b_2131_ = v___x_2132_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2184_; lean_object* v___x_2186_; 
v_nextStackPos_2184_ = l_String_Slice_posGE___redArg(v_s_2129_, v_stackPos_2150_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 3, v___x_2174_);
lean_ctor_set(v___x_2153_, 2, v_nextStackPos_2184_);
v___x_2186_ = v___x_2153_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_needle_2148_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_table_2149_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_nextStackPos_2184_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v___x_2174_);
v___x_2186_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
v_a_2130_ = v___x_2186_;
v_b_2131_ = v___x_2132_;
goto _start;
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_nextStackPos_2191_; lean_object* v___x_2193_; 
lean_dec(v_needlePos_2151_);
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = lean_nat_add(v_stackPos_2150_, v___x_2189_);
lean_dec(v_stackPos_2150_);
v_nextStackPos_2191_ = l_String_Slice_posGE___redArg(v_s_2129_, v___x_2190_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 3, v___x_2174_);
lean_ctor_set(v___x_2153_, 2, v_nextStackPos_2191_);
v___x_2193_ = v___x_2153_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_needle_2148_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_table_2149_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_nextStackPos_2191_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v___x_2174_);
v___x_2193_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
v_a_2130_ = v___x_2193_;
v_b_2131_ = v___x_2132_;
goto _start;
}
}
}
else
{
lean_object* v___x_2196_; lean_object* v_nextNeedlePos_2197_; uint8_t v___x_2198_; 
v___x_2196_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2197_ = lean_nat_add(v_needlePos_2151_, v___x_2196_);
lean_dec(v_needlePos_2151_);
v___x_2198_ = lean_nat_dec_eq(v_nextNeedlePos_2197_, v___x_2162_);
lean_dec(v___x_2162_);
if (v___x_2198_ == 0)
{
lean_object* v_nextStackPos_2199_; lean_object* v___x_2201_; 
v_nextStackPos_2199_ = lean_nat_add(v_stackPos_2150_, v___x_2196_);
lean_dec(v_stackPos_2150_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 3, v_nextNeedlePos_2197_);
lean_ctor_set(v___x_2153_, 2, v_nextStackPos_2199_);
v___x_2201_ = v___x_2153_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_needle_2148_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_table_2149_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_nextStackPos_2199_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_nextNeedlePos_2197_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
v_a_2130_ = v___x_2201_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2197_);
lean_del_object(v___x_2153_);
lean_dec(v_stackPos_2150_);
lean_dec_ref(v_table_2149_);
lean_dec_ref(v_needle_2148_);
return v___x_2198_;
}
}
}
}
}
default: 
{
return v_b_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2205_, lean_object* v_a_2206_, lean_object* v_b_2207_){
_start:
{
uint8_t v_b_boxed_2208_; uint8_t v_res_2209_; lean_object* v_r_2210_; 
v_b_boxed_2208_ = lean_unbox(v_b_2207_);
v_res_2209_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2205_, v_a_2206_, v_b_boxed_2208_);
lean_dec_ref(v_s_2205_);
v_r_2210_ = lean_box(v_res_2209_);
return v_r_2210_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2211_, lean_object* v_s_2212_){
_start:
{
lean_object* v___y_2214_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_string_utf8_byte_size(v___x_2211_);
v___x_2219_ = lean_nat_dec_eq(v___x_2218_, v___x_2217_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2211_);
lean_ctor_set(v___x_2220_, 1, v___x_2217_);
lean_ctor_set(v___x_2220_, 2, v___x_2218_);
v___x_2221_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
lean_ctor_set(v___x_2222_, 2, v___x_2217_);
lean_ctor_set(v___x_2222_, 3, v___x_2217_);
v___y_2214_ = v___x_2222_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2223_; 
lean_dec_ref(v___x_2211_);
v___x_2223_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2214_ = v___x_2223_;
goto v___jp_2213_;
}
v___jp_2213_:
{
uint8_t v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = 0;
v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2212_, v___y_2214_, v___x_2215_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2224_, lean_object* v_s_2225_){
_start:
{
uint8_t v_res_2226_; lean_object* v_r_2227_; 
v_res_2226_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2224_, v_s_2225_);
lean_dec_ref(v_s_2225_);
v_r_2227_ = lean_box(v_res_2226_);
return v_r_2227_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2228_, uint8_t v_suppressElabErrors_2229_, lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 1)
{
lean_object* v_pre_2231_; 
v_pre_2231_ = lean_ctor_get(v_x_2230_, 0);
if (lean_obj_tag(v_pre_2231_) == 0)
{
lean_object* v_str_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v_str_2232_ = lean_ctor_get(v_x_2230_, 1);
v___x_2233_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2234_ = lean_string_dec_eq(v_str_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
return v___y_2228_;
}
else
{
return v_suppressElabErrors_2229_;
}
}
else
{
return v___y_2228_;
}
}
else
{
return v___y_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2235_, lean_object* v_suppressElabErrors_2236_, lean_object* v_x_2237_){
_start:
{
uint8_t v___y_28605__boxed_2238_; uint8_t v_suppressElabErrors_boxed_2239_; uint8_t v_res_2240_; lean_object* v_r_2241_; 
v___y_28605__boxed_2238_ = lean_unbox(v___y_2235_);
v_suppressElabErrors_boxed_2239_ = lean_unbox(v_suppressElabErrors_2236_);
v_res_2240_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_28605__boxed_2238_, v_suppressElabErrors_boxed_2239_, v_x_2237_);
lean_dec(v_x_2237_);
v_r_2241_ = lean_box(v_res_2240_);
return v_r_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2242_, lean_object* v_msgData_2243_, uint8_t v_severity_2244_, uint8_t v_isSilent_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; uint8_t v___y_2256_; lean_object* v___y_2257_; uint8_t v___y_2313_; uint8_t v___y_2314_; lean_object* v___y_2315_; uint8_t v___y_2316_; lean_object* v___y_2317_; uint8_t v___y_2341_; lean_object* v___y_2342_; uint8_t v___y_2343_; uint8_t v___y_2344_; lean_object* v___y_2345_; uint8_t v___y_2349_; uint8_t v___y_2350_; uint8_t v___y_2351_; uint8_t v___x_2366_; uint8_t v___y_2368_; uint8_t v___y_2369_; uint8_t v___y_2370_; uint8_t v___y_2372_; uint8_t v___x_2384_; 
v___x_2366_ = 2;
v___x_2384_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2244_, v___x_2366_);
if (v___x_2384_ == 0)
{
v___y_2372_ = v___x_2384_;
goto v___jp_2371_;
}
else
{
uint8_t v___x_2385_; 
lean_inc_ref(v_msgData_2243_);
v___x_2385_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2243_);
v___y_2372_ = v___x_2385_;
goto v___jp_2371_;
}
v___jp_2249_:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Elab_Command_getScope___redArg(v___y_2257_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2260_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = l_Lean_Elab_Command_getScope___redArg(v___y_2257_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2295_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2295_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2295_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v_currNamespace_2266_; lean_object* v_openDecls_2267_; lean_object* v_env_2268_; lean_object* v_messages_2269_; lean_object* v_scopes_2270_; lean_object* v_usedQuotCtxts_2271_; lean_object* v_nextMacroScope_2272_; lean_object* v_maxRecDepth_2273_; lean_object* v_ngen_2274_; lean_object* v_auxDeclNGen_2275_; lean_object* v_infoState_2276_; lean_object* v_traceState_2277_; lean_object* v_snapshotTasks_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2294_; 
v___x_2265_ = lean_st_ref_take(v___y_2257_);
v_currNamespace_2266_ = lean_ctor_get(v_a_2259_, 2);
lean_inc(v_currNamespace_2266_);
lean_dec(v_a_2259_);
v_openDecls_2267_ = lean_ctor_get(v_a_2261_, 3);
lean_inc(v_openDecls_2267_);
lean_dec(v_a_2261_);
v_env_2268_ = lean_ctor_get(v___x_2265_, 0);
v_messages_2269_ = lean_ctor_get(v___x_2265_, 1);
v_scopes_2270_ = lean_ctor_get(v___x_2265_, 2);
v_usedQuotCtxts_2271_ = lean_ctor_get(v___x_2265_, 3);
v_nextMacroScope_2272_ = lean_ctor_get(v___x_2265_, 4);
v_maxRecDepth_2273_ = lean_ctor_get(v___x_2265_, 5);
v_ngen_2274_ = lean_ctor_get(v___x_2265_, 6);
v_auxDeclNGen_2275_ = lean_ctor_get(v___x_2265_, 7);
v_infoState_2276_ = lean_ctor_get(v___x_2265_, 8);
v_traceState_2277_ = lean_ctor_get(v___x_2265_, 9);
v_snapshotTasks_2278_ = lean_ctor_get(v___x_2265_, 10);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2280_ = v___x_2265_;
v_isShared_2281_ = v_isSharedCheck_2294_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_snapshotTasks_2278_);
lean_inc(v_traceState_2277_);
lean_inc(v_infoState_2276_);
lean_inc(v_auxDeclNGen_2275_);
lean_inc(v_ngen_2274_);
lean_inc(v_maxRecDepth_2273_);
lean_inc(v_nextMacroScope_2272_);
lean_inc(v_usedQuotCtxts_2271_);
lean_inc(v_scopes_2270_);
lean_inc(v_messages_2269_);
lean_inc(v_env_2268_);
lean_dec(v___x_2265_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2294_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_currNamespace_2266_);
lean_ctor_set(v___x_2282_, 1, v_openDecls_2267_);
v___x_2283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v___y_2250_);
v___x_2284_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2284_, 0, v___y_2254_);
lean_ctor_set(v___x_2284_, 1, v___y_2255_);
lean_ctor_set(v___x_2284_, 2, v___y_2251_);
lean_ctor_set(v___x_2284_, 3, v___y_2252_);
lean_ctor_set(v___x_2284_, 4, v___x_2283_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*5, v___y_2253_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*5 + 1, v___y_2256_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*5 + 2, v_isSilent_2245_);
v___x_2285_ = l_Lean_MessageLog_add(v___x_2284_, v_messages_2269_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v___x_2285_);
v___x_2287_ = v___x_2280_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_env_2268_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_scopes_2270_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_usedQuotCtxts_2271_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_nextMacroScope_2272_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v_maxRecDepth_2273_);
lean_ctor_set(v_reuseFailAlloc_2293_, 6, v_ngen_2274_);
lean_ctor_set(v_reuseFailAlloc_2293_, 7, v_auxDeclNGen_2275_);
lean_ctor_set(v_reuseFailAlloc_2293_, 8, v_infoState_2276_);
lean_ctor_set(v_reuseFailAlloc_2293_, 9, v_traceState_2277_);
lean_ctor_set(v_reuseFailAlloc_2293_, 10, v_snapshotTasks_2278_);
v___x_2287_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2288_ = lean_st_ref_set(v___y_2257_, v___x_2287_);
v___x_2289_ = lean_box(0);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2289_);
v___x_2291_ = v___x_2263_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_a_2259_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
v_a_2296_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2260_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2260_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
v_a_2304_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2258_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2258_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
v___jp_2312_:
{
lean_object* v_fileName_2318_; lean_object* v_fileMap_2319_; uint8_t v_suppressElabErrors_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2339_; 
v_fileName_2318_ = lean_ctor_get(v___y_2246_, 0);
lean_inc_ref(v_fileName_2318_);
v_fileMap_2319_ = lean_ctor_get(v___y_2246_, 1);
lean_inc_ref(v_fileMap_2319_);
v_suppressElabErrors_2320_ = lean_ctor_get_uint8(v___y_2246_, sizeof(void*)*10);
lean_dec_ref(v___y_2246_);
v___x_2321_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2243_);
v___x_2322_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2321_, v___y_2247_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2339_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2339_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_inc_ref(v_fileMap_2319_);
v___x_2327_ = l_Lean_FileMap_toPosition(v_fileMap_2319_, v___y_2315_);
lean_dec(v___y_2315_);
v___x_2328_ = l_Lean_FileMap_toPosition(v_fileMap_2319_, v___y_2317_);
lean_dec(v___y_2317_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
v___x_2330_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2320_ == 0)
{
lean_del_object(v___x_2325_);
v___y_2250_ = v_a_2323_;
v___y_2251_ = v___x_2329_;
v___y_2252_ = v___x_2330_;
v___y_2253_ = v___y_2314_;
v___y_2254_ = v_fileName_2318_;
v___y_2255_ = v___x_2327_;
v___y_2256_ = v___y_2316_;
v___y_2257_ = v___y_2247_;
goto v___jp_2249_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___f_2333_; uint8_t v___x_2334_; 
v___x_2331_ = lean_box(v___y_2313_);
v___x_2332_ = lean_box(v_suppressElabErrors_2320_);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2333_, 0, v___x_2331_);
lean_closure_set(v___f_2333_, 1, v___x_2332_);
lean_inc(v_a_2323_);
v___x_2334_ = l_Lean_MessageData_hasTag(v___f_2333_, v_a_2323_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec_ref(v___x_2329_);
lean_dec_ref(v___x_2327_);
lean_dec(v_a_2323_);
lean_dec_ref(v_fileName_2318_);
v___x_2335_ = lean_box(0);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2335_);
v___x_2337_ = v___x_2325_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
else
{
lean_del_object(v___x_2325_);
v___y_2250_ = v_a_2323_;
v___y_2251_ = v___x_2329_;
v___y_2252_ = v___x_2330_;
v___y_2253_ = v___y_2314_;
v___y_2254_ = v_fileName_2318_;
v___y_2255_ = v___x_2327_;
v___y_2256_ = v___y_2316_;
v___y_2257_ = v___y_2247_;
goto v___jp_2249_;
}
}
}
}
v___jp_2340_:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Syntax_getTailPos_x3f(v___y_2342_, v___y_2343_);
lean_dec(v___y_2342_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_inc(v___y_2345_);
v___y_2313_ = v___y_2341_;
v___y_2314_ = v___y_2343_;
v___y_2315_ = v___y_2345_;
v___y_2316_ = v___y_2344_;
v___y_2317_ = v___y_2345_;
goto v___jp_2312_;
}
else
{
lean_object* v_val_2347_; 
v_val_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_val_2347_);
lean_dec_ref(v___x_2346_);
v___y_2313_ = v___y_2341_;
v___y_2314_ = v___y_2343_;
v___y_2315_ = v___y_2345_;
v___y_2316_ = v___y_2344_;
v___y_2317_ = v_val_2347_;
goto v___jp_2312_;
}
}
v___jp_2348_:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Elab_Command_getRef___redArg(v___y_2246_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v_ref_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2352_);
v_ref_2354_ = l_Lean_replaceRef(v_ref_2242_, v_a_2353_);
lean_dec(v_a_2353_);
v___x_2355_ = l_Lean_Syntax_getPos_x3f(v_ref_2354_, v___y_2350_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___y_2341_ = v___y_2349_;
v___y_2342_ = v_ref_2354_;
v___y_2343_ = v___y_2350_;
v___y_2344_ = v___y_2351_;
v___y_2345_ = v___x_2356_;
goto v___jp_2340_;
}
else
{
lean_object* v_val_2357_; 
v_val_2357_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_val_2357_);
lean_dec_ref(v___x_2355_);
v___y_2341_ = v___y_2349_;
v___y_2342_ = v_ref_2354_;
v___y_2343_ = v___y_2350_;
v___y_2344_ = v___y_2351_;
v___y_2345_ = v_val_2357_;
goto v___jp_2340_;
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_msgData_2243_);
v_a_2358_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2352_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2352_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
v___jp_2367_:
{
if (v___y_2370_ == 0)
{
v___y_2349_ = v___y_2368_;
v___y_2350_ = v___y_2369_;
v___y_2351_ = v_severity_2244_;
goto v___jp_2348_;
}
else
{
v___y_2349_ = v___y_2368_;
v___y_2350_ = v___y_2369_;
v___y_2351_ = v___x_2366_;
goto v___jp_2348_;
}
}
v___jp_2371_:
{
if (v___y_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v_scopes_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_opts_2377_; uint8_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2373_ = lean_st_ref_get(v___y_2247_);
v_scopes_2374_ = lean_ctor_get(v___x_2373_, 2);
lean_inc(v_scopes_2374_);
lean_dec(v___x_2373_);
v___x_2375_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2376_ = l_List_head_x21___redArg(v___x_2375_, v_scopes_2374_);
lean_dec(v_scopes_2374_);
v_opts_2377_ = lean_ctor_get(v___x_2376_, 1);
lean_inc_ref(v_opts_2377_);
lean_dec(v___x_2376_);
v___x_2378_ = 1;
v___x_2379_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2244_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_dec_ref(v_opts_2377_);
v___y_2368_ = v___y_2372_;
v___y_2369_ = v___y_2372_;
v___y_2370_ = v___x_2379_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = l_Lean_warningAsError;
v___x_2381_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2377_, v___x_2380_);
lean_dec_ref(v_opts_2377_);
v___y_2368_ = v___y_2372_;
v___y_2369_ = v___y_2372_;
v___y_2370_ = v___x_2381_;
goto v___jp_2367_;
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_msgData_2243_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2386_, lean_object* v_msgData_2387_, lean_object* v_severity_2388_, lean_object* v_isSilent_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v_severity_boxed_2393_; uint8_t v_isSilent_boxed_2394_; lean_object* v_res_2395_; 
v_severity_boxed_2393_ = lean_unbox(v_severity_2388_);
v_isSilent_boxed_2394_ = lean_unbox(v_isSilent_2389_);
v_res_2395_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2386_, v_msgData_2387_, v_severity_boxed_2393_, v_isSilent_boxed_2394_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec(v_ref_2386_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2396_, lean_object* v_msgData_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
uint8_t v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = 2;
v___x_2402_ = 0;
v___x_2403_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2396_, v_msgData_2397_, v___x_2401_, v___x_2402_, v___y_2398_, v___y_2399_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2404_, lean_object* v_msgData_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2404_, v_msgData_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec(v_ref_2404_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2410_, lean_object* v___x_2411_, lean_object* v___x_2412_, lean_object* v_a_2413_, lean_object* v_b_2414_){
_start:
{
lean_object* v_it_2416_; lean_object* v_startInclusive_2417_; lean_object* v_endExclusive_2418_; 
if (lean_obj_tag(v_a_2413_) == 0)
{
lean_object* v_currPos_2423_; lean_object* v_searcher_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2453_; 
v_currPos_2423_ = lean_ctor_get(v_a_2413_, 0);
v_searcher_2424_ = lean_ctor_get(v_a_2413_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2413_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2426_ = v_a_2413_;
v_isShared_2427_ = v_isSharedCheck_2453_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_searcher_2424_);
lean_inc(v_currPos_2423_);
lean_dec(v_a_2413_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2453_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_str_2428_; lean_object* v_startInclusive_2429_; lean_object* v_endExclusive_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_str_2428_ = lean_ctor_get(v___x_2411_, 0);
v_startInclusive_2429_ = lean_ctor_get(v___x_2411_, 1);
v_endExclusive_2430_ = lean_ctor_get(v___x_2411_, 2);
v___x_2431_ = lean_nat_sub(v_endExclusive_2430_, v_startInclusive_2429_);
v___x_2432_ = lean_nat_dec_eq(v_searcher_2424_, v___x_2431_);
lean_dec(v___x_2431_);
if (v___x_2432_ == 0)
{
uint32_t v___x_2433_; lean_object* v___x_2434_; uint32_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2433_ = 10;
v___x_2434_ = lean_nat_add(v_startInclusive_2429_, v_searcher_2424_);
v___x_2435_ = lean_string_utf8_get_fast(v_str_2428_, v___x_2434_);
v___x_2436_ = lean_uint32_dec_eq(v___x_2435_, v___x_2433_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
lean_dec(v_searcher_2424_);
v___x_2437_ = lean_string_utf8_next_fast(v_str_2428_, v___x_2434_);
lean_dec(v___x_2434_);
v___x_2438_ = lean_nat_sub(v___x_2437_, v_startInclusive_2429_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2438_);
v___x_2440_ = v___x_2426_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_currPos_2423_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
v_a_2413_ = v___x_2440_;
goto _start;
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_slice_2446_; lean_object* v_nextIt_2448_; 
v___x_2443_ = lean_string_utf8_next_fast(v_str_2428_, v___x_2434_);
v___x_2444_ = lean_nat_sub(v___x_2443_, v___x_2434_);
lean_dec(v___x_2434_);
v___x_2445_ = lean_nat_add(v_searcher_2424_, v___x_2444_);
lean_dec(v___x_2444_);
v_slice_2446_ = l_String_Slice_subslice_x21(v___x_2411_, v_currPos_2423_, v_searcher_2424_);
lean_inc(v___x_2445_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2445_);
lean_ctor_set(v___x_2426_, 0, v___x_2445_);
v_nextIt_2448_ = v___x_2426_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2445_);
v_nextIt_2448_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v_startInclusive_2449_; lean_object* v_endExclusive_2450_; 
v_startInclusive_2449_ = lean_ctor_get(v_slice_2446_, 0);
lean_inc(v_startInclusive_2449_);
v_endExclusive_2450_ = lean_ctor_get(v_slice_2446_, 1);
lean_inc(v_endExclusive_2450_);
lean_dec_ref(v_slice_2446_);
v_it_2416_ = v_nextIt_2448_;
v_startInclusive_2417_ = v_startInclusive_2449_;
v_endExclusive_2418_ = v_endExclusive_2450_;
goto v___jp_2415_;
}
}
}
else
{
lean_object* v___x_2452_; 
lean_del_object(v___x_2426_);
lean_dec(v_searcher_2424_);
v___x_2452_ = lean_box(1);
lean_inc(v___x_2412_);
v_it_2416_ = v___x_2452_;
v_startInclusive_2417_ = v_currPos_2423_;
v_endExclusive_2418_ = v___x_2412_;
goto v___jp_2415_;
}
}
}
else
{
lean_dec(v___x_2412_);
lean_dec_ref(v___x_2410_);
return v_b_2414_;
}
v___jp_2415_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_inc_ref(v___x_2410_);
v___x_2419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2410_);
lean_ctor_set(v___x_2419_, 1, v_startInclusive_2417_);
lean_ctor_set(v___x_2419_, 2, v_endExclusive_2418_);
v___x_2420_ = l_String_Slice_toString(v___x_2419_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = lean_array_push(v_b_2414_, v___x_2420_);
v_a_2413_ = v_it_2416_;
v_b_2414_ = v___x_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2454_, lean_object* v___x_2455_, lean_object* v___x_2456_, lean_object* v_a_2457_, lean_object* v_b_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2454_, v___x_2455_, v___x_2456_, v_a_2457_, v_b_2458_);
lean_dec_ref(v___x_2455_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2460_, lean_object* v___x_2461_, lean_object* v___x_2462_, lean_object* v_a_2463_, lean_object* v_b_2464_){
_start:
{
lean_object* v_it_2466_; lean_object* v_startInclusive_2467_; lean_object* v_endExclusive_2468_; 
if (lean_obj_tag(v_a_2463_) == 0)
{
lean_object* v_currPos_2473_; lean_object* v_searcher_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2503_; 
v_currPos_2473_ = lean_ctor_get(v_a_2463_, 0);
v_searcher_2474_ = lean_ctor_get(v_a_2463_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2463_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2476_ = v_a_2463_;
v_isShared_2477_ = v_isSharedCheck_2503_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_searcher_2474_);
lean_inc(v_currPos_2473_);
lean_dec(v_a_2463_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2503_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_str_2478_; lean_object* v_startInclusive_2479_; lean_object* v_endExclusive_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_str_2478_ = lean_ctor_get(v___x_2461_, 0);
v_startInclusive_2479_ = lean_ctor_get(v___x_2461_, 1);
v_endExclusive_2480_ = lean_ctor_get(v___x_2461_, 2);
v___x_2481_ = lean_nat_sub(v_endExclusive_2480_, v_startInclusive_2479_);
v___x_2482_ = lean_nat_dec_eq(v_searcher_2474_, v___x_2481_);
lean_dec(v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; uint32_t v___x_2484_; uint32_t v___x_2485_; uint8_t v___x_2486_; 
v___x_2483_ = lean_nat_add(v_startInclusive_2479_, v_searcher_2474_);
v___x_2484_ = lean_string_utf8_get_fast(v_str_2478_, v___x_2483_);
v___x_2485_ = 10;
v___x_2486_ = lean_uint32_dec_eq(v___x_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
lean_dec(v_searcher_2474_);
v___x_2487_ = lean_string_utf8_next_fast(v_str_2478_, v___x_2483_);
lean_dec(v___x_2483_);
v___x_2488_ = lean_nat_sub(v___x_2487_, v_startInclusive_2479_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2488_);
v___x_2490_ = v___x_2476_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_currPos_2473_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; 
v___x_2491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2460_, v___x_2461_, v___x_2462_, v___x_2490_, v_b_2464_);
return v___x_2491_;
}
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_slice_2496_; lean_object* v_nextIt_2498_; 
v___x_2493_ = lean_string_utf8_next_fast(v_str_2478_, v___x_2483_);
v___x_2494_ = lean_nat_sub(v___x_2493_, v___x_2483_);
lean_dec(v___x_2483_);
v___x_2495_ = lean_nat_add(v_searcher_2474_, v___x_2494_);
lean_dec(v___x_2494_);
v_slice_2496_ = l_String_Slice_subslice_x21(v___x_2461_, v_currPos_2473_, v_searcher_2474_);
lean_inc(v___x_2495_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2495_);
lean_ctor_set(v___x_2476_, 0, v___x_2495_);
v_nextIt_2498_ = v___x_2476_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2495_);
v_nextIt_2498_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v_startInclusive_2499_; lean_object* v_endExclusive_2500_; 
v_startInclusive_2499_ = lean_ctor_get(v_slice_2496_, 0);
lean_inc(v_startInclusive_2499_);
v_endExclusive_2500_ = lean_ctor_get(v_slice_2496_, 1);
lean_inc(v_endExclusive_2500_);
lean_dec_ref(v_slice_2496_);
v_it_2466_ = v_nextIt_2498_;
v_startInclusive_2467_ = v_startInclusive_2499_;
v_endExclusive_2468_ = v_endExclusive_2500_;
goto v___jp_2465_;
}
}
}
else
{
lean_object* v___x_2502_; 
lean_del_object(v___x_2476_);
lean_dec(v_searcher_2474_);
v___x_2502_ = lean_box(1);
lean_inc(v___x_2462_);
v_it_2466_ = v___x_2502_;
v_startInclusive_2467_ = v_currPos_2473_;
v_endExclusive_2468_ = v___x_2462_;
goto v___jp_2465_;
}
}
}
else
{
lean_dec(v___x_2462_);
lean_dec_ref(v___x_2460_);
return v_b_2464_;
}
v___jp_2465_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_inc_ref(v___x_2460_);
v___x_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2460_);
lean_ctor_set(v___x_2469_, 1, v_startInclusive_2467_);
lean_ctor_set(v___x_2469_, 2, v_endExclusive_2468_);
v___x_2470_ = l_String_Slice_toString(v___x_2469_);
lean_dec_ref(v___x_2469_);
v___x_2471_ = lean_array_push(v_b_2464_, v___x_2470_);
v___x_2472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2460_, v___x_2461_, v___x_2462_, v_it_2466_, v___x_2471_);
return v___x_2472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2504_, lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v_a_2507_, lean_object* v_b_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2504_, v___x_2505_, v___x_2506_, v_a_2507_, v_b_2508_);
lean_dec_ref(v___x_2505_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v_infoState_2514_; uint8_t v_enabled_2515_; 
v___x_2513_ = lean_st_ref_get(v___y_2511_);
v_infoState_2514_ = lean_ctor_get(v___x_2513_, 8);
lean_inc_ref(v_infoState_2514_);
lean_dec(v___x_2513_);
v_enabled_2515_ = lean_ctor_get_uint8(v_infoState_2514_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2514_);
if (v_enabled_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_dec_ref(v_t_2510_);
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; lean_object* v_infoState_2519_; lean_object* v_env_2520_; lean_object* v_messages_2521_; lean_object* v_scopes_2522_; lean_object* v_usedQuotCtxts_2523_; lean_object* v_nextMacroScope_2524_; lean_object* v_maxRecDepth_2525_; lean_object* v_ngen_2526_; lean_object* v_auxDeclNGen_2527_; lean_object* v_traceState_2528_; lean_object* v_snapshotTasks_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2551_; 
v___x_2518_ = lean_st_ref_take(v___y_2511_);
v_infoState_2519_ = lean_ctor_get(v___x_2518_, 8);
v_env_2520_ = lean_ctor_get(v___x_2518_, 0);
v_messages_2521_ = lean_ctor_get(v___x_2518_, 1);
v_scopes_2522_ = lean_ctor_get(v___x_2518_, 2);
v_usedQuotCtxts_2523_ = lean_ctor_get(v___x_2518_, 3);
v_nextMacroScope_2524_ = lean_ctor_get(v___x_2518_, 4);
v_maxRecDepth_2525_ = lean_ctor_get(v___x_2518_, 5);
v_ngen_2526_ = lean_ctor_get(v___x_2518_, 6);
v_auxDeclNGen_2527_ = lean_ctor_get(v___x_2518_, 7);
v_traceState_2528_ = lean_ctor_get(v___x_2518_, 9);
v_snapshotTasks_2529_ = lean_ctor_get(v___x_2518_, 10);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2531_ = v___x_2518_;
v_isShared_2532_ = v_isSharedCheck_2551_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_snapshotTasks_2529_);
lean_inc(v_traceState_2528_);
lean_inc(v_infoState_2519_);
lean_inc(v_auxDeclNGen_2527_);
lean_inc(v_ngen_2526_);
lean_inc(v_maxRecDepth_2525_);
lean_inc(v_nextMacroScope_2524_);
lean_inc(v_usedQuotCtxts_2523_);
lean_inc(v_scopes_2522_);
lean_inc(v_messages_2521_);
lean_inc(v_env_2520_);
lean_dec(v___x_2518_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2551_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint8_t v_enabled_2533_; lean_object* v_assignment_2534_; lean_object* v_lazyAssignment_2535_; lean_object* v_trees_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2550_; 
v_enabled_2533_ = lean_ctor_get_uint8(v_infoState_2519_, sizeof(void*)*3);
v_assignment_2534_ = lean_ctor_get(v_infoState_2519_, 0);
v_lazyAssignment_2535_ = lean_ctor_get(v_infoState_2519_, 1);
v_trees_2536_ = lean_ctor_get(v_infoState_2519_, 2);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_infoState_2519_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2538_ = v_infoState_2519_;
v_isShared_2539_ = v_isSharedCheck_2550_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_trees_2536_);
lean_inc(v_lazyAssignment_2535_);
lean_inc(v_assignment_2534_);
lean_dec(v_infoState_2519_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2550_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = l_Lean_PersistentArray_push___redArg(v_trees_2536_, v_t_2510_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 2, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_assignment_2534_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_lazyAssignment_2535_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v___x_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2549_, sizeof(void*)*3, v_enabled_2533_);
v___x_2542_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 8, v___x_2542_);
v___x_2544_ = v___x_2531_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_env_2520_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_messages_2521_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_scopes_2522_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_usedQuotCtxts_2523_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_nextMacroScope_2524_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v_maxRecDepth_2525_);
lean_ctor_set(v_reuseFailAlloc_2548_, 6, v_ngen_2526_);
lean_ctor_set(v_reuseFailAlloc_2548_, 7, v_auxDeclNGen_2527_);
lean_ctor_set(v_reuseFailAlloc_2548_, 8, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2548_, 9, v_traceState_2528_);
lean_ctor_set(v_reuseFailAlloc_2548_, 10, v_snapshotTasks_2529_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_st_ref_set(v___y_2511_, v___x_2544_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2552_, v___y_2553_);
lean_dec(v___y_2553_);
return v_res_2555_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = lean_unsigned_to_nat(32u);
v___x_2557_ = lean_mk_empty_array_with_capacity(v___x_2556_);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2559_ = ((size_t)5ULL);
v___x_2560_ = lean_unsigned_to_nat(0u);
v___x_2561_ = lean_unsigned_to_nat(32u);
v___x_2562_ = lean_mk_empty_array_with_capacity(v___x_2561_);
v___x_2563_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2564_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v___x_2562_);
lean_ctor_set(v___x_2564_, 2, v___x_2560_);
lean_ctor_set(v___x_2564_, 3, v___x_2560_);
lean_ctor_set_usize(v___x_2564_, 4, v___x_2559_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; lean_object* v_infoState_2570_; uint8_t v_enabled_2571_; 
v___x_2569_ = lean_st_ref_get(v___y_2567_);
v_infoState_2570_ = lean_ctor_get(v___x_2569_, 8);
lean_inc_ref(v_infoState_2570_);
lean_dec(v___x_2569_);
v_enabled_2571_ = lean_ctor_get_uint8(v_infoState_2570_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2570_);
if (v_enabled_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref(v_t_2565_);
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
return v___x_2573_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_t_2565_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2575_, v___y_2567_);
return v___x_2576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_2582_, lean_object* v_edited_2583_, lean_object* v_b_2584_){
_start:
{
lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2605_; 
v_fst_2585_ = lean_ctor_get(v_b_2584_, 0);
v_snd_2586_ = lean_ctor_get(v_b_2584_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_b_2584_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2588_ = v_b_2584_;
v_isShared_2589_ = v_isSharedCheck_2605_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_inc(v_fst_2585_);
lean_dec(v_b_2584_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2605_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_nat_dec_lt(v_snd_2586_, v___x_2582_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2592_; 
if (v_isShared_2589_ == 0)
{
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_fst_2585_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_snd_2586_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
else
{
uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2594_ = 0;
v___x_2595_ = lean_array_fget_borrowed(v_edited_2583_, v_snd_2586_);
v___x_2596_ = lean_box(v___x_2594_);
lean_inc(v___x_2595_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 1, v___x_2595_);
lean_ctor_set(v___x_2588_, 0, v___x_2596_);
v___x_2598_ = v___x_2588_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2595_);
v___x_2598_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = lean_array_push(v_fst_2585_, v___x_2598_);
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = lean_nat_add(v_snd_2586_, v___x_2600_);
lean_dec(v_snd_2586_);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v_b_2584_ = v___x_2602_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_2606_, lean_object* v_edited_2607_, lean_object* v_b_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_2606_, v_edited_2607_, v_b_2608_);
lean_dec_ref(v_edited_2607_);
lean_dec(v___x_2606_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_inst_2610_, lean_object* v_edited_2611_, lean_object* v___x_2612_, lean_object* v_a_2613_, lean_object* v_b_2614_){
_start:
{
lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2640_; 
v_fst_2615_ = lean_ctor_get(v_b_2614_, 0);
v_snd_2616_ = lean_ctor_get(v_b_2614_, 1);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_b_2614_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2618_ = v_b_2614_;
v_isShared_2619_ = v_isSharedCheck_2640_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snd_2616_);
lean_inc(v_fst_2615_);
lean_dec(v_b_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2640_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
uint8_t v___y_2621_; uint8_t v___x_2636_; 
v___x_2636_ = lean_nat_dec_lt(v_snd_2616_, v___x_2612_);
if (v___x_2636_ == 0)
{
v___y_2621_ = v___x_2636_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2637_; uint8_t v___x_2638_; 
lean_inc_ref(v_inst_2610_);
v___x_2637_ = lean_array_get_borrowed(v_inst_2610_, v_edited_2611_, v_snd_2616_);
v___x_2638_ = lean_string_dec_eq(v___x_2637_, v_a_2613_);
if (v___x_2638_ == 0)
{
v___y_2621_ = v___x_2636_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2639_; 
lean_del_object(v___x_2618_);
lean_dec_ref(v_inst_2610_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_fst_2615_);
lean_ctor_set(v___x_2639_, 1, v_snd_2616_);
return v___x_2639_;
}
}
v___jp_2620_:
{
if (v___y_2621_ == 0)
{
lean_object* v___x_2623_; 
lean_dec_ref(v_inst_2610_);
if (v_isShared_2619_ == 0)
{
v___x_2623_ = v___x_2618_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_fst_2615_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_snd_2616_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2625_ = 0;
lean_inc_ref(v_inst_2610_);
v___x_2626_ = lean_array_get_borrowed(v_inst_2610_, v_edited_2611_, v_snd_2616_);
v___x_2627_ = lean_box(v___x_2625_);
lean_inc(v___x_2626_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v___x_2626_);
lean_ctor_set(v___x_2618_, 0, v___x_2627_);
v___x_2629_ = v___x_2618_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2626_);
v___x_2629_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = lean_array_push(v_fst_2615_, v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_nat_add(v_snd_2616_, v___x_2631_);
lean_dec(v_snd_2616_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2630_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v_b_2614_ = v___x_2633_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_inst_2641_, lean_object* v_edited_2642_, lean_object* v___x_2643_, lean_object* v_a_2644_, lean_object* v_b_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_inst_2641_, v_edited_2642_, v___x_2643_, v_a_2644_, v_b_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v___x_2643_);
lean_dec_ref(v_edited_2642_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_inst_2647_, lean_object* v_original_2648_, lean_object* v___x_2649_, lean_object* v_a_2650_, lean_object* v_b_2651_){
_start:
{
lean_object* v_fst_2652_; lean_object* v_snd_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2677_; 
v_fst_2652_ = lean_ctor_get(v_b_2651_, 0);
v_snd_2653_ = lean_ctor_get(v_b_2651_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_b_2651_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2655_ = v_b_2651_;
v_isShared_2656_ = v_isSharedCheck_2677_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2653_);
lean_inc(v_fst_2652_);
lean_dec(v_b_2651_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2677_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint8_t v___y_2658_; uint8_t v___x_2673_; 
v___x_2673_ = lean_nat_dec_lt(v_snd_2653_, v___x_2649_);
if (v___x_2673_ == 0)
{
v___y_2658_ = v___x_2673_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
lean_inc_ref(v_inst_2647_);
v___x_2674_ = lean_array_get_borrowed(v_inst_2647_, v_original_2648_, v_snd_2653_);
v___x_2675_ = lean_string_dec_eq(v___x_2674_, v_a_2650_);
if (v___x_2675_ == 0)
{
v___y_2658_ = v___x_2673_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2676_; 
lean_del_object(v___x_2655_);
lean_dec_ref(v_inst_2647_);
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_fst_2652_);
lean_ctor_set(v___x_2676_, 1, v_snd_2653_);
return v___x_2676_;
}
}
v___jp_2657_:
{
if (v___y_2658_ == 0)
{
lean_object* v___x_2660_; 
lean_dec_ref(v_inst_2647_);
if (v_isShared_2656_ == 0)
{
v___x_2660_ = v___x_2655_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_fst_2652_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_snd_2653_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
else
{
uint8_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2662_ = 1;
lean_inc_ref(v_inst_2647_);
v___x_2663_ = lean_array_get_borrowed(v_inst_2647_, v_original_2648_, v_snd_2653_);
v___x_2664_ = lean_box(v___x_2662_);
lean_inc(v___x_2663_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2663_);
lean_ctor_set(v___x_2655_, 0, v___x_2664_);
v___x_2666_ = v___x_2655_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2663_);
v___x_2666_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2667_ = lean_array_push(v_fst_2652_, v___x_2666_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_add(v_snd_2653_, v___x_2668_);
lean_dec(v_snd_2653_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v_b_2651_ = v___x_2670_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_inst_2678_, lean_object* v_original_2679_, lean_object* v___x_2680_, lean_object* v_a_2681_, lean_object* v_b_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_inst_2678_, v_original_2679_, v___x_2680_, v_a_2681_, v_b_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v___x_2680_);
lean_dec_ref(v_original_2679_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_inst_2684_, lean_object* v_original_2685_, lean_object* v___x_2686_, lean_object* v_edited_2687_, lean_object* v___x_2688_, lean_object* v_as_2689_, size_t v_sz_2690_, size_t v_i_2691_, lean_object* v_b_2692_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_lt(v_i_2691_, v_sz_2690_);
if (v___x_2693_ == 0)
{
lean_dec_ref(v_inst_2684_);
return v_b_2692_;
}
else
{
lean_object* v_snd_2694_; lean_object* v_fst_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2742_; 
v_snd_2694_ = lean_ctor_get(v_b_2692_, 1);
v_fst_2695_ = lean_ctor_get(v_b_2692_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_b_2692_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2697_ = v_b_2692_;
v_isShared_2698_ = v_isSharedCheck_2742_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2694_);
lean_inc(v_fst_2695_);
lean_dec(v_b_2692_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2742_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_fst_2699_; lean_object* v_snd_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2741_; 
v_fst_2699_ = lean_ctor_get(v_snd_2694_, 0);
v_snd_2700_ = lean_ctor_get(v_snd_2694_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_snd_2694_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2702_ = v_snd_2694_;
v_isShared_2703_ = v_isSharedCheck_2741_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_snd_2700_);
lean_inc(v_fst_2699_);
lean_dec(v_snd_2694_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2741_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v_a_2704_; lean_object* v___x_2706_; 
v_a_2704_ = lean_array_uget_borrowed(v_as_2689_, v_i_2691_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 1, v_fst_2699_);
lean_ctor_set(v___x_2702_, 0, v_fst_2695_);
v___x_2706_ = v___x_2702_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_fst_2695_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_fst_2699_);
v___x_2706_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v_fst_2708_; lean_object* v_snd_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2739_; 
lean_inc_ref(v_inst_2684_);
v___x_2707_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_inst_2684_, v_original_2685_, v___x_2686_, v_a_2704_, v___x_2706_);
v_fst_2708_ = lean_ctor_get(v___x_2707_, 0);
v_snd_2709_ = lean_ctor_get(v___x_2707_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2711_ = v___x_2707_;
v_isShared_2712_ = v_isSharedCheck_2739_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2709_);
lean_inc(v_fst_2708_);
lean_dec(v___x_2707_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2739_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_snd_2700_);
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_fst_2708_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_snd_2700_);
v___x_2714_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v_fst_2716_; lean_object* v_snd_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2737_; 
lean_inc_ref(v_inst_2684_);
v___x_2715_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_inst_2684_, v_edited_2687_, v___x_2688_, v_a_2704_, v___x_2714_);
v_fst_2716_ = lean_ctor_get(v___x_2715_, 0);
v_snd_2717_ = lean_ctor_get(v___x_2715_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2719_ = v___x_2715_;
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_snd_2717_);
lean_inc(v_fst_2716_);
lean_dec(v___x_2715_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = 2;
v___x_2722_ = lean_box(v___x_2721_);
lean_inc(v_a_2704_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 1, v_a_2704_);
lean_ctor_set(v___x_2719_, 0, v___x_2722_);
v___x_2724_ = v___x_2719_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_a_2704_);
v___x_2724_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2725_ = lean_array_push(v_fst_2716_, v___x_2724_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_snd_2709_, v___x_2726_);
lean_dec(v_snd_2709_);
v___x_2728_ = lean_nat_add(v_snd_2717_, v___x_2726_);
lean_dec(v_snd_2717_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2728_);
lean_ctor_set(v___x_2697_, 0, v___x_2727_);
v___x_2730_ = v___x_2697_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; 
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2725_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2691_, v___x_2732_);
v_i_2691_ = v___x_2733_;
v_b_2692_ = v___x_2731_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_inst_2743_, lean_object* v_original_2744_, lean_object* v___x_2745_, lean_object* v_edited_2746_, lean_object* v___x_2747_, lean_object* v_as_2748_, lean_object* v_sz_2749_, lean_object* v_i_2750_, lean_object* v_b_2751_){
_start:
{
size_t v_sz_boxed_2752_; size_t v_i_boxed_2753_; lean_object* v_res_2754_; 
v_sz_boxed_2752_ = lean_unbox_usize(v_sz_2749_);
lean_dec(v_sz_2749_);
v_i_boxed_2753_ = lean_unbox_usize(v_i_2750_);
lean_dec(v_i_2750_);
v_res_2754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_inst_2743_, v_original_2744_, v___x_2745_, v_edited_2746_, v___x_2747_, v_as_2748_, v_sz_boxed_2752_, v_i_boxed_2753_, v_b_2751_);
lean_dec_ref(v_as_2748_);
lean_dec(v___x_2747_);
lean_dec_ref(v_edited_2746_);
lean_dec(v___x_2745_);
lean_dec_ref(v_original_2744_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_inst_2755_, lean_object* v_edited_2756_, lean_object* v___x_2757_, lean_object* v_original_2758_, lean_object* v___x_2759_, lean_object* v_as_2760_, size_t v_sz_2761_, size_t v_i_2762_, lean_object* v_b_2763_){
_start:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_usize_dec_lt(v_i_2762_, v_sz_2761_);
if (v___x_2764_ == 0)
{
lean_dec_ref(v_inst_2755_);
return v_b_2763_;
}
else
{
lean_object* v_snd_2765_; lean_object* v_fst_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2813_; 
v_snd_2765_ = lean_ctor_get(v_b_2763_, 1);
v_fst_2766_ = lean_ctor_get(v_b_2763_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_b_2763_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2768_ = v_b_2763_;
v_isShared_2769_ = v_isSharedCheck_2813_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_snd_2765_);
lean_inc(v_fst_2766_);
lean_dec(v_b_2763_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2813_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_fst_2770_; lean_object* v_snd_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2812_; 
v_fst_2770_ = lean_ctor_get(v_snd_2765_, 0);
v_snd_2771_ = lean_ctor_get(v_snd_2765_, 1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_snd_2765_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2773_ = v_snd_2765_;
v_isShared_2774_ = v_isSharedCheck_2812_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snd_2771_);
lean_inc(v_fst_2770_);
lean_dec(v_snd_2765_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2812_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_a_2775_; lean_object* v___x_2777_; 
v_a_2775_ = lean_array_uget_borrowed(v_as_2760_, v_i_2762_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v_fst_2770_);
lean_ctor_set(v___x_2773_, 0, v_fst_2766_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_fst_2766_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_fst_2770_);
v___x_2777_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v_fst_2779_; lean_object* v_snd_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2810_; 
lean_inc_ref(v_inst_2755_);
v___x_2778_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_inst_2755_, v_original_2758_, v___x_2759_, v_a_2775_, v___x_2777_);
v_fst_2779_ = lean_ctor_get(v___x_2778_, 0);
v_snd_2780_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2782_ = v___x_2778_;
v_isShared_2783_ = v_isSharedCheck_2810_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_snd_2780_);
lean_inc(v_fst_2779_);
lean_dec(v___x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2810_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v_snd_2771_);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_fst_2779_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_snd_2771_);
v___x_2785_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v_fst_2787_; lean_object* v_snd_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2808_; 
lean_inc_ref(v_inst_2755_);
v___x_2786_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_inst_2755_, v_edited_2756_, v___x_2757_, v_a_2775_, v___x_2785_);
v_fst_2787_ = lean_ctor_get(v___x_2786_, 0);
v_snd_2788_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2808_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_snd_2788_);
lean_inc(v_fst_2787_);
lean_dec(v___x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2808_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2792_ = 2;
v___x_2793_ = lean_box(v___x_2792_);
lean_inc(v_a_2775_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 1, v_a_2775_);
lean_ctor_set(v___x_2790_, 0, v___x_2793_);
v___x_2795_ = v___x_2790_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_a_2775_);
v___x_2795_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2796_ = lean_array_push(v_fst_2787_, v___x_2795_);
v___x_2797_ = lean_unsigned_to_nat(1u);
v___x_2798_ = lean_nat_add(v_snd_2780_, v___x_2797_);
lean_dec(v_snd_2780_);
v___x_2799_ = lean_nat_add(v_snd_2788_, v___x_2797_);
lean_dec(v_snd_2788_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___x_2799_);
lean_ctor_set(v___x_2768_, 0, v___x_2798_);
v___x_2801_ = v___x_2768_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; size_t v___x_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2796_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = ((size_t)1ULL);
v___x_2804_ = lean_usize_add(v_i_2762_, v___x_2803_);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_inst_2755_, v_original_2758_, v___x_2759_, v_edited_2756_, v___x_2757_, v_as_2760_, v_sz_2761_, v___x_2804_, v___x_2802_);
return v___x_2805_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_inst_2814_, lean_object* v_edited_2815_, lean_object* v___x_2816_, lean_object* v_original_2817_, lean_object* v___x_2818_, lean_object* v_as_2819_, lean_object* v_sz_2820_, lean_object* v_i_2821_, lean_object* v_b_2822_){
_start:
{
size_t v_sz_boxed_2823_; size_t v_i_boxed_2824_; lean_object* v_res_2825_; 
v_sz_boxed_2823_ = lean_unbox_usize(v_sz_2820_);
lean_dec(v_sz_2820_);
v_i_boxed_2824_ = lean_unbox_usize(v_i_2821_);
lean_dec(v_i_2821_);
v_res_2825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_inst_2814_, v_edited_2815_, v___x_2816_, v_original_2817_, v___x_2818_, v_as_2819_, v_sz_boxed_2823_, v_i_boxed_2824_, v_b_2822_);
lean_dec_ref(v_as_2819_);
lean_dec(v___x_2818_);
lean_dec_ref(v_original_2817_);
lean_dec(v___x_2816_);
lean_dec_ref(v_edited_2815_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2826_, lean_object* v_x_2827_){
_start:
{
if (lean_obj_tag(v_x_2827_) == 0)
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_box(0);
return v___x_2828_;
}
else
{
lean_object* v_key_2829_; lean_object* v_value_2830_; lean_object* v_tail_2831_; uint8_t v___x_2832_; 
v_key_2829_ = lean_ctor_get(v_x_2827_, 0);
v_value_2830_ = lean_ctor_get(v_x_2827_, 1);
v_tail_2831_ = lean_ctor_get(v_x_2827_, 2);
v___x_2832_ = lean_string_dec_eq(v_key_2829_, v_a_2826_);
if (v___x_2832_ == 0)
{
v_x_2827_ = v_tail_2831_;
goto _start;
}
else
{
lean_object* v___x_2834_; 
lean_inc(v_value_2830_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_value_2830_);
return v___x_2834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2835_, lean_object* v_x_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2835_, v_x_2836_);
lean_dec(v_x_2836_);
lean_dec_ref(v_a_2835_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_buckets_2840_; lean_object* v___x_2841_; uint64_t v___x_2842_; uint64_t v___x_2843_; uint64_t v___x_2844_; uint64_t v_fold_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_buckets_2840_ = lean_ctor_get(v_m_2838_, 1);
v___x_2841_ = lean_array_get_size(v_buckets_2840_);
v___x_2842_ = lean_string_hash(v_a_2839_);
v___x_2843_ = 32ULL;
v___x_2844_ = lean_uint64_shift_right(v___x_2842_, v___x_2843_);
v_fold_2845_ = lean_uint64_xor(v___x_2842_, v___x_2844_);
v___x_2846_ = 16ULL;
v___x_2847_ = lean_uint64_shift_right(v_fold_2845_, v___x_2846_);
v___x_2848_ = lean_uint64_xor(v_fold_2845_, v___x_2847_);
v___x_2849_ = lean_uint64_to_usize(v___x_2848_);
v___x_2850_ = lean_usize_of_nat(v___x_2841_);
v___x_2851_ = ((size_t)1ULL);
v___x_2852_ = lean_usize_sub(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_usize_land(v___x_2849_, v___x_2852_);
v___x_2854_ = lean_array_uget_borrowed(v_buckets_2840_, v___x_2853_);
v___x_2855_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2839_, v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2856_, v_a_2857_);
lean_dec_ref(v_a_2857_);
lean_dec_ref(v_m_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2859_, lean_object* v_b_2860_, lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 0)
{
lean_dec(v_b_2860_);
lean_dec_ref(v_a_2859_);
return v_x_2861_;
}
else
{
lean_object* v_key_2862_; lean_object* v_value_2863_; lean_object* v_tail_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2876_; 
v_key_2862_ = lean_ctor_get(v_x_2861_, 0);
v_value_2863_ = lean_ctor_get(v_x_2861_, 1);
v_tail_2864_ = lean_ctor_get(v_x_2861_, 2);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_x_2861_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2866_ = v_x_2861_;
v_isShared_2867_ = v_isSharedCheck_2876_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_tail_2864_);
lean_inc(v_value_2863_);
lean_inc(v_key_2862_);
lean_dec(v_x_2861_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2876_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_string_dec_eq(v_key_2862_, v_a_2859_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2869_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2859_, v_b_2860_, v_tail_2864_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 2, v___x_2869_);
v___x_2871_ = v___x_2866_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_key_2862_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_value_2863_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_value_2863_);
lean_dec(v_key_2862_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v_b_2860_);
lean_ctor_set(v___x_2866_, 0, v_a_2859_);
v___x_2874_ = v___x_2866_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2859_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_b_2860_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_tail_2864_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2877_, lean_object* v_x_2878_){
_start:
{
if (lean_obj_tag(v_x_2878_) == 0)
{
uint8_t v___x_2879_; 
v___x_2879_ = 0;
return v___x_2879_;
}
else
{
lean_object* v_key_2880_; lean_object* v_tail_2881_; uint8_t v___x_2882_; 
v_key_2880_ = lean_ctor_get(v_x_2878_, 0);
v_tail_2881_ = lean_ctor_get(v_x_2878_, 2);
v___x_2882_ = lean_string_dec_eq(v_key_2880_, v_a_2877_);
if (v___x_2882_ == 0)
{
v_x_2878_ = v_tail_2881_;
goto _start;
}
else
{
return v___x_2882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2884_, lean_object* v_x_2885_){
_start:
{
uint8_t v_res_2886_; lean_object* v_r_2887_; 
v_res_2886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2884_, v_x_2885_);
lean_dec(v_x_2885_);
lean_dec_ref(v_a_2884_);
v_r_2887_ = lean_box(v_res_2886_);
return v_r_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
return v_x_2888_;
}
else
{
lean_object* v_key_2890_; lean_object* v_value_2891_; lean_object* v_tail_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2915_; 
v_key_2890_ = lean_ctor_get(v_x_2889_, 0);
v_value_2891_ = lean_ctor_get(v_x_2889_, 1);
v_tail_2892_ = lean_ctor_get(v_x_2889_, 2);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2894_ = v_x_2889_;
v_isShared_2895_ = v_isSharedCheck_2915_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_tail_2892_);
lean_inc(v_value_2891_);
lean_inc(v_key_2890_);
lean_dec(v_x_2889_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2915_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; uint64_t v___x_2897_; uint64_t v___x_2898_; uint64_t v___x_2899_; uint64_t v_fold_2900_; uint64_t v___x_2901_; uint64_t v___x_2902_; uint64_t v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2896_ = lean_array_get_size(v_x_2888_);
v___x_2897_ = lean_string_hash(v_key_2890_);
v___x_2898_ = 32ULL;
v___x_2899_ = lean_uint64_shift_right(v___x_2897_, v___x_2898_);
v_fold_2900_ = lean_uint64_xor(v___x_2897_, v___x_2899_);
v___x_2901_ = 16ULL;
v___x_2902_ = lean_uint64_shift_right(v_fold_2900_, v___x_2901_);
v___x_2903_ = lean_uint64_xor(v_fold_2900_, v___x_2902_);
v___x_2904_ = lean_uint64_to_usize(v___x_2903_);
v___x_2905_ = lean_usize_of_nat(v___x_2896_);
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_sub(v___x_2905_, v___x_2906_);
v___x_2908_ = lean_usize_land(v___x_2904_, v___x_2907_);
v___x_2909_ = lean_array_uget_borrowed(v_x_2888_, v___x_2908_);
lean_inc(v___x_2909_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 2, v___x_2909_);
v___x_2911_ = v___x_2894_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_key_2890_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_value_2891_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_array_uset(v_x_2888_, v___x_2908_, v___x_2911_);
v_x_2888_ = v___x_2912_;
v_x_2889_ = v_tail_2892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2916_, lean_object* v_source_2917_, lean_object* v_target_2918_){
_start:
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_array_get_size(v_source_2917_);
v___x_2920_ = lean_nat_dec_lt(v_i_2916_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_dec_ref(v_source_2917_);
lean_dec(v_i_2916_);
return v_target_2918_;
}
else
{
lean_object* v_es_2921_; lean_object* v___x_2922_; lean_object* v_source_2923_; lean_object* v_target_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_es_2921_ = lean_array_fget(v_source_2917_, v_i_2916_);
v___x_2922_ = lean_box(0);
v_source_2923_ = lean_array_fset(v_source_2917_, v_i_2916_, v___x_2922_);
v_target_2924_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2918_, v_es_2921_);
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_add(v_i_2916_, v___x_2925_);
lean_dec(v_i_2916_);
v_i_2916_ = v___x_2926_;
v_source_2917_ = v_source_2923_;
v_target_2918_ = v_target_2924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2928_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_nbuckets_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2929_ = lean_array_get_size(v_data_2928_);
v___x_2930_ = lean_unsigned_to_nat(2u);
v_nbuckets_2931_ = lean_nat_mul(v___x_2929_, v___x_2930_);
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_mk_array(v_nbuckets_2931_, v___x_2933_);
v___x_2935_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2932_, v_data_2928_, v___x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2936_, lean_object* v_a_2937_, lean_object* v_b_2938_){
_start:
{
lean_object* v_size_2939_; lean_object* v_buckets_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2983_; 
v_size_2939_ = lean_ctor_get(v_m_2936_, 0);
v_buckets_2940_ = lean_ctor_get(v_m_2936_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_m_2936_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2942_ = v_m_2936_;
v_isShared_2943_ = v_isSharedCheck_2983_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_buckets_2940_);
lean_inc(v_size_2939_);
lean_dec(v_m_2936_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2983_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; uint64_t v_fold_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; lean_object* v_bkt_2957_; uint8_t v___x_2958_; 
v___x_2944_ = lean_array_get_size(v_buckets_2940_);
v___x_2945_ = lean_string_hash(v_a_2937_);
v___x_2946_ = 32ULL;
v___x_2947_ = lean_uint64_shift_right(v___x_2945_, v___x_2946_);
v_fold_2948_ = lean_uint64_xor(v___x_2945_, v___x_2947_);
v___x_2949_ = 16ULL;
v___x_2950_ = lean_uint64_shift_right(v_fold_2948_, v___x_2949_);
v___x_2951_ = lean_uint64_xor(v_fold_2948_, v___x_2950_);
v___x_2952_ = lean_uint64_to_usize(v___x_2951_);
v___x_2953_ = lean_usize_of_nat(v___x_2944_);
v___x_2954_ = ((size_t)1ULL);
v___x_2955_ = lean_usize_sub(v___x_2953_, v___x_2954_);
v___x_2956_ = lean_usize_land(v___x_2952_, v___x_2955_);
v_bkt_2957_ = lean_array_uget_borrowed(v_buckets_2940_, v___x_2956_);
v___x_2958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2937_, v_bkt_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v_size_x27_2960_; lean_object* v___x_2961_; lean_object* v_buckets_x27_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2959_ = lean_unsigned_to_nat(1u);
v_size_x27_2960_ = lean_nat_add(v_size_2939_, v___x_2959_);
lean_dec(v_size_2939_);
lean_inc(v_bkt_2957_);
v___x_2961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2961_, 0, v_a_2937_);
lean_ctor_set(v___x_2961_, 1, v_b_2938_);
lean_ctor_set(v___x_2961_, 2, v_bkt_2957_);
v_buckets_x27_2962_ = lean_array_uset(v_buckets_2940_, v___x_2956_, v___x_2961_);
v___x_2963_ = lean_unsigned_to_nat(4u);
v___x_2964_ = lean_nat_mul(v_size_x27_2960_, v___x_2963_);
v___x_2965_ = lean_unsigned_to_nat(3u);
v___x_2966_ = lean_nat_div(v___x_2964_, v___x_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_array_get_size(v_buckets_x27_2962_);
v___x_2968_ = lean_nat_dec_le(v___x_2966_, v___x_2967_);
lean_dec(v___x_2966_);
if (v___x_2968_ == 0)
{
lean_object* v_val_2969_; lean_object* v___x_2971_; 
v_val_2969_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_2962_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_val_2969_);
lean_ctor_set(v___x_2942_, 0, v_size_x27_2960_);
v___x_2971_ = v___x_2942_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_size_x27_2960_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_val_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
else
{
lean_object* v___x_2974_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_buckets_x27_2962_);
lean_ctor_set(v___x_2942_, 0, v_size_x27_2960_);
v___x_2974_ = v___x_2942_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_size_x27_2960_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_buckets_x27_2962_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v___x_2976_; lean_object* v_buckets_x27_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
lean_inc(v_bkt_2957_);
v___x_2976_ = lean_box(0);
v_buckets_x27_2977_ = lean_array_uset(v_buckets_2940_, v___x_2956_, v___x_2976_);
v___x_2978_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2937_, v_b_2938_, v_bkt_2957_);
v___x_2979_ = lean_array_uset(v_buckets_x27_2977_, v___x_2956_, v___x_2978_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v___x_2979_);
v___x_2981_ = v___x_2942_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_size_2939_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_2984_, lean_object* v_index_2985_, lean_object* v_val_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_2984_, v_val_2986_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2988_ = lean_unsigned_to_nat(1u);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_index_2985_);
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2988_);
lean_ctor_set(v___x_2992_, 1, v___x_2989_);
lean_ctor_set(v___x_2992_, 2, v___x_2990_);
lean_ctor_set(v___x_2992_, 3, v___x_2991_);
v___x_2993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2984_, v_val_2986_, v___x_2992_);
return v___x_2993_;
}
else
{
lean_object* v_val_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3015_; 
v_val_2994_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2996_ = v___x_2987_;
v_isShared_2997_ = v_isSharedCheck_3015_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_val_2994_);
lean_dec(v___x_2987_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3015_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v_leftCount_2998_; lean_object* v_rightCount_2999_; lean_object* v_rightIndex_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3013_; 
v_leftCount_2998_ = lean_ctor_get(v_val_2994_, 0);
v_rightCount_2999_ = lean_ctor_get(v_val_2994_, 2);
v_rightIndex_3000_ = lean_ctor_get(v_val_2994_, 3);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_val_2994_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v_val_2994_, 1);
lean_dec(v_unused_3014_);
v___x_3002_ = v_val_2994_;
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_rightIndex_3000_);
lean_inc(v_rightCount_2999_);
lean_inc(v_leftCount_2998_);
lean_dec(v_val_2994_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_add(v_leftCount_2998_, v___x_3004_);
lean_dec(v_leftCount_2998_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v_index_2985_);
v___x_3007_ = v___x_2996_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_index_2985_);
v___x_3007_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3009_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v___x_3007_);
lean_ctor_set(v___x_3002_, 0, v___x_3005_);
v___x_3009_ = v___x_3002_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_rightCount_2999_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_rightIndex_3000_);
v___x_3009_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2984_, v_val_2986_, v___x_3009_);
return v___x_3010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3016_, lean_object* v_fst_3017_, lean_object* v___x_3018_, lean_object* v_fst_3019_, lean_object* v_a_3020_, lean_object* v_b_3021_){
_start:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_nat_dec_lt(v_a_3020_, v_upperBound_3016_);
if (v___x_3022_ == 0)
{
lean_dec(v_a_3020_);
return v_b_3021_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3023_ = l_Subarray_get___redArg(v_fst_3019_, v_a_3020_);
lean_inc(v_a_3020_);
v___x_3024_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3021_, v_a_3020_, v___x_3023_);
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_add(v_a_3020_, v___x_3025_);
lean_dec(v_a_3020_);
v_a_3020_ = v___x_3026_;
v_b_3021_ = v___x_3024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3028_, lean_object* v_fst_3029_, lean_object* v___x_3030_, lean_object* v_fst_3031_, lean_object* v_a_3032_, lean_object* v_b_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3028_, v_fst_3029_, v___x_3030_, v_fst_3031_, v_a_3032_, v_b_3033_);
lean_dec_ref(v_fst_3031_);
lean_dec(v___x_3030_);
lean_dec_ref(v_fst_3029_);
lean_dec(v_upperBound_3028_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3035_, lean_object* v_x_3036_){
_start:
{
if (lean_obj_tag(v_x_3036_) == 0)
{
lean_inc(v_x_3035_);
return v_x_3035_;
}
else
{
lean_object* v_key_3037_; lean_object* v_value_3038_; lean_object* v_tail_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_key_3037_ = lean_ctor_get(v_x_3036_, 0);
v_value_3038_ = lean_ctor_get(v_x_3036_, 1);
v_tail_3039_ = lean_ctor_get(v_x_3036_, 2);
v___x_3040_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3035_, v_tail_3039_);
lean_inc(v_value_3038_);
lean_inc(v_key_3037_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v_key_3037_);
lean_ctor_set(v___x_3041_, 1, v_value_3038_);
v___x_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v___x_3040_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3043_, lean_object* v_x_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3043_, v_x_3044_);
lean_dec(v_x_3044_);
lean_dec(v_x_3043_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3046_, size_t v_i_3047_, size_t v_stop_3048_, lean_object* v_b_3049_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_eq(v_i_3047_, v_stop_3048_);
if (v___x_3050_ == 0)
{
size_t v___x_3051_; size_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3051_ = ((size_t)1ULL);
v___x_3052_ = lean_usize_sub(v_i_3047_, v___x_3051_);
v___x_3053_ = lean_array_uget_borrowed(v_as_3046_, v___x_3052_);
v___x_3054_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3049_, v___x_3053_);
lean_dec(v_b_3049_);
v_i_3047_ = v___x_3052_;
v_b_3049_ = v___x_3054_;
goto _start;
}
else
{
return v_b_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3056_, lean_object* v_i_3057_, lean_object* v_stop_3058_, lean_object* v_b_3059_){
_start:
{
size_t v_i_boxed_3060_; size_t v_stop_boxed_3061_; lean_object* v_res_3062_; 
v_i_boxed_3060_ = lean_unbox_usize(v_i_3057_);
lean_dec(v_i_3057_);
v_stop_boxed_3061_ = lean_unbox_usize(v_stop_3058_);
lean_dec(v_stop_3058_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3056_, v_i_boxed_3060_, v_stop_boxed_3061_, v_b_3059_);
lean_dec_ref(v_as_3056_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3063_, lean_object* v_right_3064_, lean_object* v_pref_3065_){
_start:
{
lean_object* v_start_3066_; lean_object* v_stop_3067_; lean_object* v_i_3068_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_start_3066_ = lean_ctor_get(v_left_3063_, 1);
v_stop_3067_ = lean_ctor_get(v_left_3063_, 2);
v_i_3068_ = lean_array_get_size(v_pref_3065_);
v___x_3074_ = lean_nat_sub(v_stop_3067_, v_start_3066_);
v___x_3075_ = lean_nat_dec_lt(v_i_3068_, v___x_3074_);
lean_dec(v___x_3074_);
if (v___x_3075_ == 0)
{
goto v___jp_3069_;
}
else
{
lean_object* v_start_3076_; lean_object* v_stop_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_start_3076_ = lean_ctor_get(v_right_3064_, 1);
v_stop_3077_ = lean_ctor_get(v_right_3064_, 2);
v___x_3078_ = lean_nat_sub(v_stop_3077_, v_start_3076_);
v___x_3079_ = lean_nat_dec_lt(v_i_3068_, v___x_3078_);
lean_dec(v___x_3078_);
if (v___x_3079_ == 0)
{
goto v___jp_3069_;
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3080_ = l_Subarray_get___redArg(v_left_3063_, v_i_3068_);
v___x_3081_ = l_Subarray_get___redArg(v_right_3064_, v_i_3068_);
v___x_3082_ = lean_string_dec_eq(v___x_3080_, v___x_3081_);
lean_dec(v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_dec(v___x_3080_);
v___x_3083_ = l_Subarray_drop___redArg(v_left_3063_, v_i_3068_);
v___x_3084_ = l_Subarray_drop___redArg(v_right_3064_, v_i_3068_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_pref_3065_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
return v___x_3086_;
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_array_push(v_pref_3065_, v___x_3080_);
v_pref_3065_ = v___x_3087_;
goto _start;
}
}
}
v___jp_3069_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = l_Subarray_drop___redArg(v_left_3063_, v_i_3068_);
v___x_3071_ = l_Subarray_drop___redArg(v_right_3064_, v_i_3068_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_pref_3065_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3091_, lean_object* v_right_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3094_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3091_, v_right_3092_, v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3095_, lean_object* v_b_3096_){
_start:
{
lean_object* v_array_3097_; lean_object* v_start_3098_; lean_object* v_stop_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3112_; 
v_array_3097_ = lean_ctor_get(v_a_3095_, 0);
v_start_3098_ = lean_ctor_get(v_a_3095_, 1);
v_stop_3099_ = lean_ctor_get(v_a_3095_, 2);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_a_3095_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3101_ = v_a_3095_;
v_isShared_3102_ = v_isSharedCheck_3112_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_stop_3099_);
lean_inc(v_start_3098_);
lean_inc(v_array_3097_);
lean_dec(v_a_3095_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3112_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_nat_dec_lt(v_start_3098_, v_stop_3099_);
if (v___x_3103_ == 0)
{
lean_del_object(v___x_3101_);
lean_dec(v_stop_3099_);
lean_dec(v_start_3098_);
lean_dec_ref(v_array_3097_);
return v_b_3096_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3104_ = lean_unsigned_to_nat(1u);
v___x_3105_ = lean_nat_add(v_start_3098_, v___x_3104_);
lean_inc_ref(v_array_3097_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v___x_3105_);
v___x_3107_ = v___x_3101_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_array_3097_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_stop_3099_);
v___x_3107_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_array_fget(v_array_3097_, v_start_3098_);
lean_dec(v_start_3098_);
lean_dec_ref(v_array_3097_);
v___x_3109_ = lean_array_push(v_b_3096_, v___x_3108_);
v_a_3095_ = v___x_3107_;
v_b_3096_ = v___x_3109_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3113_, lean_object* v_right_3114_, lean_object* v_i_3115_){
_start:
{
lean_object* v_start_3116_; lean_object* v_stop_3117_; lean_object* v___x_3118_; uint8_t v___x_3132_; 
v_start_3116_ = lean_ctor_get(v_left_3113_, 1);
v_stop_3117_ = lean_ctor_get(v_left_3113_, 2);
v___x_3118_ = lean_nat_sub(v_stop_3117_, v_start_3116_);
v___x_3132_ = lean_nat_dec_lt(v_i_3115_, v___x_3118_);
if (v___x_3132_ == 0)
{
goto v___jp_3119_;
}
else
{
lean_object* v_start_3133_; lean_object* v_stop_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_start_3133_ = lean_ctor_get(v_right_3114_, 1);
v_stop_3134_ = lean_ctor_get(v_right_3114_, 2);
v___x_3135_ = lean_nat_sub(v_stop_3134_, v_start_3133_);
v___x_3136_ = lean_nat_dec_lt(v_i_3115_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_dec(v___x_3135_);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3137_ = lean_nat_sub(v___x_3118_, v_i_3115_);
lean_dec(v___x_3118_);
v___x_3138_ = lean_unsigned_to_nat(1u);
v___x_3139_ = lean_nat_sub(v___x_3137_, v___x_3138_);
v___x_3140_ = l_Subarray_get___redArg(v_left_3113_, v___x_3139_);
lean_dec(v___x_3139_);
v___x_3141_ = lean_nat_sub(v___x_3135_, v_i_3115_);
lean_dec(v___x_3135_);
v___x_3142_ = lean_nat_sub(v___x_3141_, v___x_3138_);
v___x_3143_ = l_Subarray_get___redArg(v_right_3114_, v___x_3142_);
lean_dec(v___x_3142_);
v___x_3144_ = lean_string_dec_eq(v___x_3140_, v___x_3143_);
lean_dec(v___x_3143_);
lean_dec(v___x_3140_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v_i_3115_);
lean_inc_ref(v_left_3113_);
v___x_3145_ = l_Subarray_take___redArg(v_left_3113_, v___x_3137_);
v___x_3146_ = l_Subarray_take___redArg(v_right_3114_, v___x_3141_);
lean_dec(v___x_3141_);
v___x_3147_ = l_Subarray_drop___redArg(v_left_3113_, v___x_3137_);
lean_dec(v___x_3137_);
v___x_3148_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3149_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3147_, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3146_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3145_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
return v___x_3151_;
}
else
{
lean_object* v___x_3152_; 
lean_dec(v___x_3141_);
lean_dec(v___x_3137_);
v___x_3152_ = lean_nat_add(v_i_3115_, v___x_3138_);
lean_dec(v_i_3115_);
v_i_3115_ = v___x_3152_;
goto _start;
}
}
}
v___jp_3119_:
{
lean_object* v_start_3120_; lean_object* v_stop_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_start_3120_ = lean_ctor_get(v_right_3114_, 1);
v_stop_3121_ = lean_ctor_get(v_right_3114_, 2);
v___x_3122_ = lean_nat_sub(v___x_3118_, v_i_3115_);
lean_dec(v___x_3118_);
lean_inc_ref(v_left_3113_);
v___x_3123_ = l_Subarray_take___redArg(v_left_3113_, v___x_3122_);
v___x_3124_ = lean_nat_sub(v_stop_3121_, v_start_3120_);
v___x_3125_ = lean_nat_sub(v___x_3124_, v_i_3115_);
lean_dec(v_i_3115_);
lean_dec(v___x_3124_);
v___x_3126_ = l_Subarray_take___redArg(v_right_3114_, v___x_3125_);
lean_dec(v___x_3125_);
v___x_3127_ = l_Subarray_drop___redArg(v_left_3113_, v___x_3122_);
lean_dec(v___x_3122_);
v___x_3128_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3129_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3127_, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3126_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3123_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3154_, lean_object* v_right_3155_){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3154_, v_right_3155_, v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3158_, lean_object* v_b_3159_){
_start:
{
if (lean_obj_tag(v_as_x27_3158_) == 0)
{
return v_b_3159_;
}
else
{
lean_object* v_head_3160_; lean_object* v_snd_3161_; lean_object* v_leftIndex_3162_; 
v_head_3160_ = lean_ctor_get(v_as_x27_3158_, 0);
lean_inc(v_head_3160_);
v_snd_3161_ = lean_ctor_get(v_head_3160_, 1);
lean_inc(v_snd_3161_);
v_leftIndex_3162_ = lean_ctor_get(v_snd_3161_, 1);
lean_inc(v_leftIndex_3162_);
if (lean_obj_tag(v_leftIndex_3162_) == 1)
{
lean_object* v_rightIndex_3163_; 
v_rightIndex_3163_ = lean_ctor_get(v_snd_3161_, 3);
lean_inc(v_rightIndex_3163_);
if (lean_obj_tag(v_rightIndex_3163_) == 1)
{
if (lean_obj_tag(v_b_3159_) == 0)
{
lean_object* v_tail_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3194_; 
v_tail_3164_ = lean_ctor_get(v_as_x27_3158_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_as_x27_3158_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v_as_x27_3158_, 0);
lean_dec(v_unused_3195_);
v___x_3166_ = v_as_x27_3158_;
v_isShared_3167_ = v_isSharedCheck_3194_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_tail_3164_);
lean_dec(v_as_x27_3158_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3194_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v_fst_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3192_; 
v_fst_3168_ = lean_ctor_get(v_head_3160_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_head_3160_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v_head_3160_, 1);
lean_dec(v_unused_3193_);
v___x_3170_ = v_head_3160_;
v_isShared_3171_ = v_isSharedCheck_3192_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_fst_3168_);
lean_dec(v_head_3160_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3192_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_leftCount_3172_; lean_object* v_rightCount_3173_; lean_object* v_val_3174_; lean_object* v_val_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3191_; 
v_leftCount_3172_ = lean_ctor_get(v_snd_3161_, 0);
lean_inc(v_leftCount_3172_);
v_rightCount_3173_ = lean_ctor_get(v_snd_3161_, 2);
lean_inc(v_rightCount_3173_);
lean_dec(v_snd_3161_);
v_val_3174_ = lean_ctor_get(v_leftIndex_3162_, 0);
lean_inc(v_val_3174_);
lean_dec_ref(v_leftIndex_3162_);
v_val_3175_ = lean_ctor_get(v_rightIndex_3163_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_rightIndex_3163_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3177_ = v_rightIndex_3163_;
v_isShared_3178_ = v_isSharedCheck_3191_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_val_3175_);
lean_dec(v_rightIndex_3163_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3191_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_nat_add(v_leftCount_3172_, v_rightCount_3173_);
lean_dec(v_rightCount_3173_);
lean_dec(v_leftCount_3172_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v_val_3175_);
lean_ctor_set(v___x_3170_, 0, v_val_3174_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_val_3174_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_val_3175_);
v___x_3181_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set_tag(v___x_3166_, 0);
lean_ctor_set(v___x_3166_, 1, v___x_3181_);
lean_ctor_set(v___x_3166_, 0, v_fst_3168_);
v___x_3183_ = v___x_3166_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_fst_3168_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3179_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3184_);
v___x_3186_ = v___x_3177_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
v_as_x27_3158_ = v_tail_3164_;
v_b_3159_ = v___x_3186_;
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
lean_object* v_val_3196_; lean_object* v_tail_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3238_; 
v_val_3196_ = lean_ctor_get(v_b_3159_, 0);
lean_inc(v_val_3196_);
v_tail_3197_ = lean_ctor_get(v_as_x27_3158_, 1);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_as_x27_3158_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_as_x27_3158_, 0);
lean_dec(v_unused_3239_);
v___x_3199_ = v_as_x27_3158_;
v_isShared_3200_ = v_isSharedCheck_3238_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_tail_3197_);
lean_dec(v_as_x27_3158_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3238_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_fst_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3236_; 
v_fst_3201_ = lean_ctor_get(v_head_3160_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_head_3160_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_head_3160_, 1);
lean_dec(v_unused_3237_);
v___x_3203_ = v_head_3160_;
v_isShared_3204_ = v_isSharedCheck_3236_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_fst_3201_);
lean_dec(v_head_3160_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3236_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_leftCount_3205_; lean_object* v_rightCount_3206_; lean_object* v_val_3207_; lean_object* v_val_3208_; lean_object* v_fst_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3234_; 
v_leftCount_3205_ = lean_ctor_get(v_snd_3161_, 0);
lean_inc(v_leftCount_3205_);
v_rightCount_3206_ = lean_ctor_get(v_snd_3161_, 2);
lean_inc(v_rightCount_3206_);
lean_dec(v_snd_3161_);
v_val_3207_ = lean_ctor_get(v_leftIndex_3162_, 0);
lean_inc(v_val_3207_);
lean_dec_ref(v_leftIndex_3162_);
v_val_3208_ = lean_ctor_get(v_rightIndex_3163_, 0);
lean_inc(v_val_3208_);
lean_dec_ref(v_rightIndex_3163_);
v_fst_3209_ = lean_ctor_get(v_val_3196_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_val_3196_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v_val_3196_, 1);
lean_dec(v_unused_3235_);
v___x_3211_ = v_val_3196_;
v_isShared_3212_ = v_isSharedCheck_3234_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_fst_3209_);
lean_dec(v_val_3196_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3234_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = lean_nat_add(v_leftCount_3205_, v_rightCount_3206_);
lean_dec(v_rightCount_3206_);
lean_dec(v_leftCount_3205_);
v___x_3214_ = lean_nat_dec_lt(v___x_3213_, v_fst_3209_);
lean_dec(v_fst_3209_);
if (v___x_3214_ == 0)
{
lean_dec(v___x_3213_);
lean_del_object(v___x_3211_);
lean_dec(v_val_3208_);
lean_dec(v_val_3207_);
lean_del_object(v___x_3203_);
lean_dec(v_fst_3201_);
lean_del_object(v___x_3199_);
v_as_x27_3158_ = v_tail_3197_;
goto _start;
}
else
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3232_; 
v_isSharedCheck_3232_ = !lean_is_exclusive(v_b_3159_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v_b_3159_, 0);
lean_dec(v_unused_3233_);
v___x_3217_ = v_b_3159_;
v_isShared_3218_ = v_isSharedCheck_3232_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v_b_3159_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3232_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v_val_3208_);
lean_ctor_set(v___x_3211_, 0, v_val_3207_);
v___x_3220_ = v___x_3211_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_val_3207_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_val_3208_);
v___x_3220_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 1, v___x_3220_);
v___x_3222_ = v___x_3203_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_fst_3201_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 0);
lean_ctor_set(v___x_3199_, 1, v___x_3222_);
lean_ctor_set(v___x_3199_, 0, v___x_3213_);
v___x_3224_ = v___x_3199_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3224_);
v___x_3226_ = v___x_3217_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
v_as_x27_3158_ = v_tail_3197_;
v_b_3159_ = v___x_3226_;
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
lean_object* v_tail_3240_; 
lean_dec(v_rightIndex_3163_);
lean_dec_ref(v_leftIndex_3162_);
lean_dec(v_snd_3161_);
lean_dec(v_head_3160_);
v_tail_3240_ = lean_ctor_get(v_as_x27_3158_, 1);
lean_inc(v_tail_3240_);
lean_dec_ref(v_as_x27_3158_);
v_as_x27_3158_ = v_tail_3240_;
goto _start;
}
}
else
{
lean_object* v_tail_3242_; 
lean_dec(v_leftIndex_3162_);
lean_dec(v_snd_3161_);
lean_dec(v_head_3160_);
v_tail_3242_ = lean_ctor_get(v_as_x27_3158_, 1);
lean_inc(v_tail_3242_);
lean_dec_ref(v_as_x27_3158_);
v_as_x27_3158_ = v_tail_3242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3244_, lean_object* v_index_3245_, lean_object* v_val_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3244_, v_val_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3248_ = lean_unsigned_to_nat(0u);
v___x_3249_ = lean_box(0);
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_index_3245_);
v___x_3252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3248_);
lean_ctor_set(v___x_3252_, 1, v___x_3249_);
lean_ctor_set(v___x_3252_, 2, v___x_3250_);
lean_ctor_set(v___x_3252_, 3, v___x_3251_);
v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3244_, v_val_3246_, v___x_3252_);
return v___x_3253_;
}
else
{
lean_object* v_val_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3275_; 
v_val_3254_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3256_ = v___x_3247_;
v_isShared_3257_ = v_isSharedCheck_3275_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_val_3254_);
lean_dec(v___x_3247_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3275_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v_leftCount_3258_; lean_object* v_leftIndex_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3272_; 
v_leftCount_3258_ = lean_ctor_get(v_val_3254_, 0);
v_leftIndex_3259_ = lean_ctor_get(v_val_3254_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_val_3254_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; lean_object* v_unused_3274_; 
v_unused_3273_ = lean_ctor_get(v_val_3254_, 3);
lean_dec(v_unused_3273_);
v_unused_3274_ = lean_ctor_get(v_val_3254_, 2);
lean_dec(v_unused_3274_);
v___x_3261_ = v_val_3254_;
v_isShared_3262_ = v_isSharedCheck_3272_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_leftIndex_3259_);
lean_inc(v_leftCount_3258_);
lean_dec(v_val_3254_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3272_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_nat_add(v_leftCount_3258_, v___x_3263_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v_index_3245_);
v___x_3266_ = v___x_3256_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_index_3245_);
v___x_3266_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3268_; 
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 3, v___x_3266_);
lean_ctor_set(v___x_3261_, 2, v___x_3264_);
v___x_3268_ = v___x_3261_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_leftCount_3258_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_leftIndex_3259_);
lean_ctor_set(v_reuseFailAlloc_3270_, 2, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3270_, 3, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3244_, v_val_3246_, v___x_3268_);
return v___x_3269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3276_, lean_object* v___x_3277_, lean_object* v_fst_3278_, lean_object* v___x_3279_, lean_object* v_a_3280_, lean_object* v_b_3281_){
_start:
{
uint8_t v___x_3282_; 
v___x_3282_ = lean_nat_dec_lt(v_a_3280_, v_upperBound_3276_);
if (v___x_3282_ == 0)
{
lean_dec(v_a_3280_);
return v_b_3281_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3283_ = l_Subarray_get___redArg(v_fst_3278_, v_a_3280_);
lean_inc(v_a_3280_);
v___x_3284_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3281_, v_a_3280_, v___x_3283_);
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_nat_add(v_a_3280_, v___x_3285_);
lean_dec(v_a_3280_);
v_a_3280_ = v___x_3286_;
v_b_3281_ = v___x_3284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3288_, lean_object* v___x_3289_, lean_object* v_fst_3290_, lean_object* v___x_3291_, lean_object* v_a_3292_, lean_object* v_b_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3288_, v___x_3289_, v_fst_3290_, v___x_3291_, v_a_3292_, v_b_3293_);
lean_dec(v___x_3291_);
lean_dec_ref(v_fst_3290_);
lean_dec(v___x_3289_);
lean_dec(v_upperBound_3288_);
return v_res_3294_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_unsigned_to_nat(16u);
v___x_3297_ = lean_mk_array(v___x_3296_, v___x_3295_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v_hist_3300_; 
v___x_3298_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3299_ = lean_unsigned_to_nat(0u);
v_hist_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3300_, 0, v___x_3299_);
lean_ctor_set(v_hist_3300_, 1, v___x_3298_);
return v_hist_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3301_, lean_object* v_right_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v_snd_3304_; lean_object* v_fst_3305_; lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v___x_3308_; lean_object* v_snd_3309_; lean_object* v_fst_3310_; lean_object* v_fst_3311_; lean_object* v_snd_3312_; lean_object* v_start_3313_; lean_object* v_stop_3314_; lean_object* v___x_3315_; lean_object* v_hist_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v_start_3319_; lean_object* v_stop_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v_buckets_3323_; lean_object* v___x_3324_; lean_object* v___y_3326_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3303_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3301_, v_right_3302_);
v_snd_3304_ = lean_ctor_get(v___x_3303_, 1);
lean_inc(v_snd_3304_);
v_fst_3305_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_fst_3305_);
lean_dec_ref(v___x_3303_);
v_fst_3306_ = lean_ctor_get(v_snd_3304_, 0);
lean_inc(v_fst_3306_);
v_snd_3307_ = lean_ctor_get(v_snd_3304_, 1);
lean_inc(v_snd_3307_);
lean_dec(v_snd_3304_);
v___x_3308_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3306_, v_snd_3307_);
v_snd_3309_ = lean_ctor_get(v___x_3308_, 1);
lean_inc(v_snd_3309_);
v_fst_3310_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_fst_3310_);
lean_dec_ref(v___x_3308_);
v_fst_3311_ = lean_ctor_get(v_snd_3309_, 0);
lean_inc(v_fst_3311_);
v_snd_3312_ = lean_ctor_get(v_snd_3309_, 1);
lean_inc(v_snd_3312_);
lean_dec(v_snd_3309_);
v_start_3313_ = lean_ctor_get(v_fst_3310_, 1);
v_stop_3314_ = lean_ctor_get(v_fst_3310_, 2);
v___x_3315_ = lean_unsigned_to_nat(0u);
v_hist_3316_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3317_ = lean_nat_sub(v_stop_3314_, v_start_3313_);
v___x_3318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3317_, v_fst_3311_, v___x_3317_, v_fst_3310_, v___x_3315_, v_hist_3316_);
v_start_3319_ = lean_ctor_get(v_fst_3311_, 1);
v_stop_3320_ = lean_ctor_get(v_fst_3311_, 2);
v___x_3321_ = lean_nat_sub(v_stop_3320_, v_start_3319_);
v___x_3322_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3321_, v___x_3321_, v_fst_3311_, v___x_3317_, v___x_3315_, v___x_3318_);
lean_dec(v___x_3317_);
lean_dec(v___x_3321_);
v_buckets_3323_ = lean_ctor_get(v___x_3322_, 1);
lean_inc_ref(v_buckets_3323_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = lean_box(0);
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_array_get_size(v_buckets_3323_);
v___x_3354_ = lean_nat_dec_lt(v___x_3315_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_dec_ref(v_buckets_3323_);
v___y_3326_ = v___x_3352_;
goto v___jp_3325_;
}
else
{
size_t v___x_3355_; size_t v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = lean_usize_of_nat(v___x_3353_);
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3323_, v___x_3355_, v___x_3356_, v___x_3352_);
lean_dec_ref(v_buckets_3323_);
v___y_3326_ = v___x_3357_;
goto v___jp_3325_;
}
v___jp_3325_:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3326_, v___x_3324_);
if (lean_obj_tag(v___x_3327_) == 1)
{
lean_object* v_val_3328_; lean_object* v_snd_3329_; lean_object* v_snd_3330_; lean_object* v_fst_3331_; lean_object* v_fst_3332_; lean_object* v_snd_3333_; lean_object* v___x_3334_; lean_object* v_fst_3335_; lean_object* v_snd_3336_; lean_object* v___x_3337_; lean_object* v_fst_3338_; lean_object* v_snd_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v_val_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3328_);
lean_dec_ref(v___x_3327_);
v_snd_3329_ = lean_ctor_get(v_val_3328_, 1);
lean_inc(v_snd_3329_);
lean_dec(v_val_3328_);
v_snd_3330_ = lean_ctor_get(v_snd_3329_, 1);
lean_inc(v_snd_3330_);
v_fst_3331_ = lean_ctor_get(v_snd_3329_, 0);
lean_inc(v_fst_3331_);
lean_dec(v_snd_3329_);
v_fst_3332_ = lean_ctor_get(v_snd_3330_, 0);
lean_inc(v_fst_3332_);
v_snd_3333_ = lean_ctor_get(v_snd_3330_, 1);
lean_inc(v_snd_3333_);
lean_dec(v_snd_3330_);
v___x_3334_ = l_Subarray_split___redArg(v_fst_3310_, v_fst_3332_);
lean_dec(v_fst_3332_);
v_fst_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_fst_3335_);
v_snd_3336_ = lean_ctor_get(v___x_3334_, 1);
lean_inc(v_snd_3336_);
lean_dec_ref(v___x_3334_);
v___x_3337_ = l_Subarray_split___redArg(v_fst_3311_, v_snd_3333_);
lean_dec(v_snd_3333_);
v_fst_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_fst_3338_);
v_snd_3339_ = lean_ctor_get(v___x_3337_, 1);
lean_inc(v_snd_3339_);
lean_dec_ref(v___x_3337_);
v___x_3340_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3335_, v_fst_3338_);
v___x_3341_ = l_Array_append___redArg(v_fst_3305_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = lean_unsigned_to_nat(1u);
v___x_3343_ = lean_mk_empty_array_with_capacity(v___x_3342_);
v___x_3344_ = lean_array_push(v___x_3343_, v_fst_3331_);
v___x_3345_ = l_Array_append___redArg(v___x_3341_, v___x_3344_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = l_Subarray_drop___redArg(v_snd_3336_, v___x_3342_);
v___x_3347_ = l_Subarray_drop___redArg(v_snd_3339_, v___x_3342_);
v___x_3348_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3346_, v___x_3347_);
v___x_3349_ = l_Array_append___redArg(v___x_3345_, v___x_3348_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = l_Array_append___redArg(v___x_3349_, v_snd_3312_);
lean_dec(v_snd_3312_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; 
lean_dec(v___x_3327_);
lean_dec(v_fst_3311_);
lean_dec(v_fst_3310_);
v___x_3351_ = l_Array_append___redArg(v_fst_3305_, v_snd_3312_);
lean_dec(v_snd_3312_);
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3358_, lean_object* v_original_3359_, lean_object* v_b_3360_){
_start:
{
lean_object* v_fst_3361_; lean_object* v_snd_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3381_; 
v_fst_3361_ = lean_ctor_get(v_b_3360_, 0);
v_snd_3362_ = lean_ctor_get(v_b_3360_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_b_3360_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3364_ = v_b_3360_;
v_isShared_3365_ = v_isSharedCheck_3381_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_snd_3362_);
lean_inc(v_fst_3361_);
lean_dec(v_b_3360_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3381_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_nat_dec_lt(v_snd_3362_, v___x_3358_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3368_; 
if (v_isShared_3365_ == 0)
{
v___x_3368_ = v___x_3364_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_fst_3361_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_snd_3362_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
else
{
uint8_t v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3370_ = 1;
v___x_3371_ = lean_array_fget_borrowed(v_original_3359_, v_snd_3362_);
v___x_3372_ = lean_box(v___x_3370_);
lean_inc(v___x_3371_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v___x_3371_);
lean_ctor_set(v___x_3364_, 0, v___x_3372_);
v___x_3374_ = v___x_3364_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3371_);
v___x_3374_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3375_ = lean_array_push(v_fst_3361_, v___x_3374_);
v___x_3376_ = lean_unsigned_to_nat(1u);
v___x_3377_ = lean_nat_add(v_snd_3362_, v___x_3376_);
lean_dec(v_snd_3362_);
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3375_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v_b_3360_ = v___x_3378_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3382_, lean_object* v_original_3383_, lean_object* v_b_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3382_, v_original_3383_, v_b_3384_);
lean_dec_ref(v_original_3383_);
lean_dec(v___x_3382_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3386_, size_t v_i_3387_, lean_object* v_bs_3388_){
_start:
{
uint8_t v___x_3389_; 
v___x_3389_ = lean_usize_dec_lt(v_i_3387_, v_sz_3386_);
if (v___x_3389_ == 0)
{
return v_bs_3388_;
}
else
{
lean_object* v_v_3390_; lean_object* v___x_3391_; lean_object* v_bs_x27_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v_v_3390_ = lean_array_uget(v_bs_3388_, v_i_3387_);
v___x_3391_ = lean_unsigned_to_nat(0u);
v_bs_x27_3392_ = lean_array_uset(v_bs_3388_, v_i_3387_, v___x_3391_);
v___x_3393_ = 0;
v___x_3394_ = lean_box(v___x_3393_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v_v_3390_);
v___x_3396_ = ((size_t)1ULL);
v___x_3397_ = lean_usize_add(v_i_3387_, v___x_3396_);
v___x_3398_ = lean_array_uset(v_bs_x27_3392_, v_i_3387_, v___x_3395_);
v_i_3387_ = v___x_3397_;
v_bs_3388_ = v___x_3398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3400_, lean_object* v_i_3401_, lean_object* v_bs_3402_){
_start:
{
size_t v_sz_boxed_3403_; size_t v_i_boxed_3404_; lean_object* v_res_3405_; 
v_sz_boxed_3403_ = lean_unbox_usize(v_sz_3400_);
lean_dec(v_sz_3400_);
v_i_boxed_3404_ = lean_unbox_usize(v_i_3401_);
lean_dec(v_i_3401_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3403_, v_i_boxed_3404_, v_bs_3402_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_bs_3408_){
_start:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3409_ == 0)
{
return v_bs_3408_;
}
else
{
lean_object* v_v_3410_; lean_object* v___x_3411_; lean_object* v_bs_x27_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; size_t v___x_3416_; size_t v___x_3417_; lean_object* v___x_3418_; 
v_v_3410_ = lean_array_uget(v_bs_3408_, v_i_3407_);
v___x_3411_ = lean_unsigned_to_nat(0u);
v_bs_x27_3412_ = lean_array_uset(v_bs_3408_, v_i_3407_, v___x_3411_);
v___x_3413_ = 1;
v___x_3414_ = lean_box(v___x_3413_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v_v_3410_);
v___x_3416_ = ((size_t)1ULL);
v___x_3417_ = lean_usize_add(v_i_3407_, v___x_3416_);
v___x_3418_ = lean_array_uset(v_bs_x27_3412_, v_i_3407_, v___x_3415_);
v_i_3407_ = v___x_3417_;
v_bs_3408_ = v___x_3418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3420_, lean_object* v_i_3421_, lean_object* v_bs_3422_){
_start:
{
size_t v_sz_boxed_3423_; size_t v_i_boxed_3424_; lean_object* v_res_3425_; 
v_sz_boxed_3423_ = lean_unbox_usize(v_sz_3420_);
lean_dec(v_sz_3420_);
v_i_boxed_3424_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3423_, v_i_boxed_3424_, v_bs_3422_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_inst_3433_, lean_object* v_original_3434_, lean_object* v_edited_3435_){
_start:
{
lean_object* v_i_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; 
v_i_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = lean_array_get_size(v_original_3434_);
v___x_3438_ = lean_nat_dec_lt(v_i_3436_, v___x_3437_);
if (v___x_3438_ == 0)
{
size_t v_sz_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
lean_dec_ref(v_original_3434_);
lean_dec_ref(v_inst_3433_);
v_sz_3439_ = lean_array_size(v_edited_3435_);
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3439_, v___x_3440_, v_edited_3435_);
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = lean_array_get_size(v_edited_3435_);
v___x_3443_ = lean_nat_dec_lt(v_i_3436_, v___x_3442_);
if (v___x_3443_ == 0)
{
size_t v_sz_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
lean_dec_ref(v_edited_3435_);
lean_dec_ref(v_inst_3433_);
v_sz_3444_ = lean_array_size(v_original_3434_);
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3444_, v___x_3445_, v_original_3434_);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v_ds_3449_; lean_object* v___x_3450_; size_t v_sz_3451_; size_t v___x_3452_; lean_object* v___x_3453_; lean_object* v_snd_3454_; lean_object* v_fst_3455_; lean_object* v_fst_3456_; lean_object* v_snd_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3476_; 
lean_inc_ref(v_original_3434_);
v___x_3447_ = l_Array_toSubarray___redArg(v_original_3434_, v_i_3436_, v___x_3437_);
lean_inc_ref(v_edited_3435_);
v___x_3448_ = l_Array_toSubarray___redArg(v_edited_3435_, v_i_3436_, v___x_3442_);
v_ds_3449_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3447_, v___x_3448_);
v___x_3450_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3451_ = lean_array_size(v_ds_3449_);
v___x_3452_ = ((size_t)0ULL);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_inst_3433_, v_edited_3435_, v___x_3442_, v_original_3434_, v___x_3437_, v_ds_3449_, v_sz_3451_, v___x_3452_, v___x_3450_);
lean_dec_ref(v_ds_3449_);
v_snd_3454_ = lean_ctor_get(v___x_3453_, 1);
lean_inc(v_snd_3454_);
v_fst_3455_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_fst_3455_);
lean_dec_ref(v___x_3453_);
v_fst_3456_ = lean_ctor_get(v_snd_3454_, 0);
v_snd_3457_ = lean_ctor_get(v_snd_3454_, 1);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_snd_3454_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3459_ = v_snd_3454_;
v_isShared_3460_ = v_isSharedCheck_3476_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_snd_3457_);
lean_inc(v_fst_3456_);
lean_dec(v_snd_3454_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3476_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v_fst_3456_);
lean_ctor_set(v___x_3459_, 0, v_fst_3455_);
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_fst_3455_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_fst_3456_);
v___x_3462_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v_fst_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3473_; 
v___x_3463_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3437_, v_original_3434_, v___x_3462_);
lean_dec_ref(v_original_3434_);
v_fst_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; 
v_unused_3474_ = lean_ctor_get(v___x_3463_, 1);
lean_dec(v_unused_3474_);
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_fst_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v_snd_3457_);
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_fst_3464_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_snd_3457_);
v___x_3469_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v_fst_3471_; 
v___x_3470_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3442_, v_edited_3435_, v___x_3469_);
lean_dec_ref(v_edited_3435_);
v_fst_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_fst_3471_);
lean_dec_ref(v___x_3470_);
return v_fst_3471_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3477_, lean_object* v_x_3478_, lean_object* v_x_3479_){
_start:
{
if (lean_obj_tag(v_x_3478_) == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = l_List_reverse___redArg(v_x_3479_);
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
else
{
lean_object* v_head_3483_; lean_object* v_tail_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3493_; 
v_head_3483_ = lean_ctor_get(v_x_3478_, 0);
v_tail_3484_ = lean_ctor_get(v_x_3478_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_x_3478_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3486_ = v_x_3478_;
v_isShared_3487_ = v_isSharedCheck_3493_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_tail_3484_);
lean_inc(v_head_3483_);
lean_dec(v_x_3478_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3493_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3488_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3483_, v___y_3477_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v_x_3479_);
lean_ctor_set(v___x_3486_, 0, v___x_3488_);
v___x_3490_ = v___x_3486_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_x_3479_);
v___x_3490_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
v_x_3478_ = v_tail_3484_;
v_x_3479_ = v___x_3490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3494_, v_x_3495_, v_x_3496_);
lean_dec(v___y_3494_);
return v_res_3498_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
return v___x_3501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = l_Lean_MessageLog_empty;
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; uint8_t v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; uint8_t v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_dc_x3f_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3515_);
v___x_3765_ = l_Lean_Syntax_isOfKind(v_x_3515_, v___x_3764_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; 
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_x_3515_);
v___x_3766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3766_;
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
v___x_3767_ = lean_unsigned_to_nat(0u);
v___x_3768_ = l_Lean_Syntax_getArg(v_x_3515_, v___x_3767_);
v___x_3769_ = l_Lean_Syntax_isNone(v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; uint8_t v___x_3771_; 
v___x_3770_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3768_);
v___x_3771_ = l_Lean_Syntax_matchesNull(v___x_3768_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; 
lean_dec(v___x_3768_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_x_3515_);
v___x_3772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3772_;
}
else
{
lean_object* v_dc_x3f_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v_dc_x3f_3773_ = l_Lean_Syntax_getArg(v___x_3768_, v___x_3767_);
lean_dec(v___x_3768_);
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3773_);
v___x_3775_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3773_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; 
lean_dec(v_dc_x3f_3773_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_x_3515_);
v___x_3776_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3776_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3777_, 0, v_dc_x3f_3773_);
v_dc_x3f_3745_ = v___x_3777_;
v___y_3746_ = v_a_3516_;
v___y_3747_ = v_a_3517_;
goto v___jp_3744_;
}
}
}
else
{
lean_object* v___x_3778_; 
lean_dec(v___x_3768_);
v___x_3778_ = lean_box(0);
v_dc_x3f_3745_ = v___x_3778_;
v___y_3746_ = v_a_3516_;
v___y_3747_ = v_a_3517_;
goto v___jp_3744_;
}
}
v___jp_3519_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3525_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3526_ = l_Lean_stringToMessageData(v___y_3524_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
lean_inc_ref(v___y_3523_);
v___x_3528_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3522_, v___x_3527_, v___y_3523_, v___y_3520_);
lean_dec(v___y_3522_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3549_; 
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v___x_3528_, 0);
lean_dec(v_unused_3550_);
v___x_3530_ = v___x_3528_;
v_isShared_3531_ = v_isSharedCheck_3549_;
goto v_resetjp_3529_;
}
else
{
lean_dec(v___x_3528_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3549_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_Elab_Command_getRef___redArg(v___y_3523_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3532_);
v___x_3534_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v___y_3521_);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3533_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set_tag(v___x_3530_, 10);
lean_ctor_set(v___x_3530_, 0, v___x_3536_);
v___x_3538_ = v___x_3530_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3538_, v___y_3523_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3523_);
return v___x_3539_;
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_del_object(v___x_3530_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
v_a_3541_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3532_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
return v___x_3528_;
}
}
v___jp_3551_:
{
if (v___y_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v_env_3562_; lean_object* v_scopes_3563_; lean_object* v_usedQuotCtxts_3564_; lean_object* v_nextMacroScope_3565_; lean_object* v_maxRecDepth_3566_; lean_object* v_ngen_3567_; lean_object* v_auxDeclNGen_3568_; lean_object* v_infoState_3569_; lean_object* v_traceState_3570_; lean_object* v_snapshotTasks_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v___y_3554_);
v___x_3561_ = lean_st_ref_take(v___y_3553_);
v_env_3562_ = lean_ctor_get(v___x_3561_, 0);
v_scopes_3563_ = lean_ctor_get(v___x_3561_, 2);
v_usedQuotCtxts_3564_ = lean_ctor_get(v___x_3561_, 3);
v_nextMacroScope_3565_ = lean_ctor_get(v___x_3561_, 4);
v_maxRecDepth_3566_ = lean_ctor_get(v___x_3561_, 5);
v_ngen_3567_ = lean_ctor_get(v___x_3561_, 6);
v_auxDeclNGen_3568_ = lean_ctor_get(v___x_3561_, 7);
v_infoState_3569_ = lean_ctor_get(v___x_3561_, 8);
v_traceState_3570_ = lean_ctor_get(v___x_3561_, 9);
v_snapshotTasks_3571_ = lean_ctor_get(v___x_3561_, 10);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v___x_3561_, 1);
lean_dec(v_unused_3599_);
v___x_3573_ = v___x_3561_;
v_isShared_3574_ = v_isSharedCheck_3598_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_snapshotTasks_3571_);
lean_inc(v_traceState_3570_);
lean_inc(v_infoState_3569_);
lean_inc(v_auxDeclNGen_3568_);
lean_inc(v_ngen_3567_);
lean_inc(v_maxRecDepth_3566_);
lean_inc(v_nextMacroScope_3565_);
lean_inc(v_usedQuotCtxts_3564_);
lean_inc(v_scopes_3563_);
lean_inc(v_env_3562_);
lean_dec(v___x_3561_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3598_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___y_3552_);
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_env_3562_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___y_3552_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_scopes_3563_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_usedQuotCtxts_3564_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v_nextMacroScope_3565_);
lean_ctor_set(v_reuseFailAlloc_3597_, 5, v_maxRecDepth_3566_);
lean_ctor_set(v_reuseFailAlloc_3597_, 6, v_ngen_3567_);
lean_ctor_set(v_reuseFailAlloc_3597_, 7, v_auxDeclNGen_3568_);
lean_ctor_set(v_reuseFailAlloc_3597_, 8, v_infoState_3569_);
lean_ctor_set(v_reuseFailAlloc_3597_, 9, v_traceState_3570_);
lean_ctor_set(v_reuseFailAlloc_3597_, 10, v_snapshotTasks_3571_);
v___x_3576_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v_scopes_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_opts_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3577_ = lean_st_ref_set(v___y_3553_, v___x_3576_);
v___x_3578_ = lean_st_ref_get(v___y_3553_);
v_scopes_3579_ = lean_ctor_get(v___x_3578_, 2);
lean_inc(v_scopes_3579_);
lean_dec(v___x_3578_);
v___x_3580_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3581_ = l_List_head_x21___redArg(v___x_3580_, v_scopes_3579_);
lean_dec(v_scopes_3579_);
v_opts_3582_ = lean_ctor_get(v___x_3581_, 1);
lean_inc_ref(v_opts_3582_);
lean_dec(v___x_3581_);
v___x_3583_ = l_guard__msgs_diff;
v___x_3584_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3582_, v___x_3583_);
lean_dec_ref(v_opts_3582_);
if (v___x_3584_ == 0)
{
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_inc_ref(v___y_3557_);
v___y_3520_ = v___y_3553_;
v___y_3521_ = v___y_3557_;
v___y_3522_ = v___y_3558_;
v___y_3523_ = v___y_3559_;
v___y_3524_ = v___y_3557_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3585_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_3586_ = lean_string_utf8_byte_size(v___y_3556_);
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3556_);
v___x_3587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3587_, 0, v___y_3556_);
lean_ctor_set(v___x_3587_, 1, v___y_3555_);
lean_ctor_set(v___x_3587_, 2, v___x_3586_);
v___x_3588_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3587_);
v___x_3589_ = lean_mk_empty_array_with_capacity(v___y_3555_);
lean_inc_ref(v___x_3589_);
v___x_3590_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3556_, v___x_3587_, v___x_3586_, v___x_3588_, v___x_3589_);
lean_dec_ref(v___x_3587_);
v___x_3591_ = lean_string_utf8_byte_size(v___y_3557_);
lean_inc_ref(v___y_3557_);
v___x_3592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3592_, 0, v___y_3557_);
lean_ctor_set(v___x_3592_, 1, v___y_3555_);
lean_ctor_set(v___x_3592_, 2, v___x_3591_);
v___x_3593_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3592_);
lean_inc_ref(v___y_3557_);
v___x_3594_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3557_, v___x_3592_, v___x_3591_, v___x_3593_, v___x_3589_);
lean_dec_ref(v___x_3592_);
v___x_3595_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3585_, v___x_3590_, v___x_3594_);
v___x_3596_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3595_);
lean_dec_ref(v___x_3595_);
v___y_3520_ = v___y_3553_;
v___y_3521_ = v___y_3557_;
v___y_3522_ = v___y_3558_;
v___y_3523_ = v___y_3559_;
v___y_3524_ = v___x_3596_;
goto v___jp_3519_;
}
}
}
}
else
{
lean_object* v___x_3600_; lean_object* v_env_3601_; lean_object* v_scopes_3602_; lean_object* v_usedQuotCtxts_3603_; lean_object* v_nextMacroScope_3604_; lean_object* v_maxRecDepth_3605_; lean_object* v_ngen_3606_; lean_object* v_auxDeclNGen_3607_; lean_object* v_infoState_3608_; lean_object* v_traceState_3609_; lean_object* v_snapshotTasks_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3552_);
v___x_3600_ = lean_st_ref_take(v___y_3553_);
v_env_3601_ = lean_ctor_get(v___x_3600_, 0);
v_scopes_3602_ = lean_ctor_get(v___x_3600_, 2);
v_usedQuotCtxts_3603_ = lean_ctor_get(v___x_3600_, 3);
v_nextMacroScope_3604_ = lean_ctor_get(v___x_3600_, 4);
v_maxRecDepth_3605_ = lean_ctor_get(v___x_3600_, 5);
v_ngen_3606_ = lean_ctor_get(v___x_3600_, 6);
v_auxDeclNGen_3607_ = lean_ctor_get(v___x_3600_, 7);
v_infoState_3608_ = lean_ctor_get(v___x_3600_, 8);
v_traceState_3609_ = lean_ctor_get(v___x_3600_, 9);
v_snapshotTasks_3610_ = lean_ctor_get(v___x_3600_, 10);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v___x_3600_, 1);
lean_dec(v_unused_3621_);
v___x_3612_ = v___x_3600_;
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_snapshotTasks_3610_);
lean_inc(v_traceState_3609_);
lean_inc(v_infoState_3608_);
lean_inc(v_auxDeclNGen_3607_);
lean_inc(v_ngen_3606_);
lean_inc(v_maxRecDepth_3605_);
lean_inc(v_nextMacroScope_3604_);
lean_inc(v_usedQuotCtxts_3603_);
lean_inc(v_scopes_3602_);
lean_inc(v_env_3601_);
lean_dec(v___x_3600_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v___y_3554_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_env_3601_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___y_3554_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_scopes_3602_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_usedQuotCtxts_3603_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_nextMacroScope_3604_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_maxRecDepth_3605_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_ngen_3606_);
lean_ctor_set(v_reuseFailAlloc_3619_, 7, v_auxDeclNGen_3607_);
lean_ctor_set(v_reuseFailAlloc_3619_, 8, v_infoState_3608_);
lean_ctor_set(v_reuseFailAlloc_3619_, 9, v_traceState_3609_);
lean_ctor_set(v_reuseFailAlloc_3619_, 10, v_snapshotTasks_3610_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = lean_st_ref_set(v___y_3553_, v___x_3615_);
lean_dec(v___y_3553_);
v___x_3617_ = lean_box(0);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
}
}
v___jp_3622_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v_a_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_str_3645_; lean_object* v_startInclusive_3646_; lean_object* v_endExclusive_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3662_; 
v___x_3635_ = l_Lean_MessageLog_toList(v___y_3633_);
lean_dec(v___y_3633_);
v___x_3636_ = lean_box(0);
v___x_3637_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3634_, v___x_3635_, v___x_3636_);
lean_dec(v___y_3634_);
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___x_3637_);
v___x_3639_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3632_, v_a_3638_);
v___x_3640_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3641_ = l_String_intercalate(v___x_3640_, v___x_3639_);
v___x_3642_ = lean_string_utf8_byte_size(v___x_3641_);
lean_inc(v___y_3628_);
v___x_3643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set(v___x_3643_, 1, v___y_3628_);
lean_ctor_set(v___x_3643_, 2, v___x_3642_);
v___x_3644_ = l_String_Slice_trimAscii(v___x_3643_);
v_str_3645_ = lean_ctor_get(v___x_3644_, 0);
v_startInclusive_3646_ = lean_ctor_get(v___x_3644_, 1);
v_endExclusive_3647_ = lean_ctor_get(v___x_3644_, 2);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3649_ = v___x_3644_;
v_isShared_3650_ = v_isSharedCheck_3662_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_endExclusive_3647_);
lean_inc(v_startInclusive_3646_);
lean_inc(v_str_3645_);
lean_dec(v___x_3644_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3662_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_string_utf8_extract(v_str_3645_, v_startInclusive_3646_, v_endExclusive_3647_);
lean_dec(v_endExclusive_3647_);
lean_dec(v_startInclusive_3646_);
lean_dec_ref(v_str_3645_);
if (v___y_3629_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
lean_del_object(v___x_3649_);
lean_inc_ref(v___y_3627_);
v___x_3652_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3623_, v___y_3627_);
lean_inc_ref(v___x_3651_);
v___x_3653_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3623_, v___x_3651_);
v___x_3654_ = lean_string_dec_eq(v___x_3652_, v___x_3653_);
lean_dec_ref(v___x_3653_);
lean_dec_ref(v___x_3652_);
v___y_3552_ = v___y_3624_;
v___y_3553_ = v___y_3625_;
v___y_3554_ = v___y_3626_;
v___y_3555_ = v___y_3628_;
v___y_3556_ = v___y_3627_;
v___y_3557_ = v___x_3651_;
v___y_3558_ = v___y_3630_;
v___y_3559_ = v___y_3631_;
v___y_3560_ = v___x_3654_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3659_; 
lean_inc_ref(v___x_3651_);
v___x_3655_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3623_, v___x_3651_);
lean_inc_ref(v___y_3627_);
v___x_3656_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3623_, v___y_3627_);
v___x_3657_ = lean_string_utf8_byte_size(v___x_3655_);
lean_inc(v___y_3628_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 2, v___x_3657_);
lean_ctor_set(v___x_3649_, 1, v___y_3628_);
lean_ctor_set(v___x_3649_, 0, v___x_3655_);
v___x_3659_ = v___x_3649_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v___y_3628_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
uint8_t v___x_3660_; 
v___x_3660_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3656_, v___x_3659_);
lean_dec_ref(v___x_3659_);
v___y_3552_ = v___y_3624_;
v___y_3553_ = v___y_3625_;
v___y_3554_ = v___y_3626_;
v___y_3555_ = v___y_3628_;
v___y_3556_ = v___y_3627_;
v___y_3557_ = v___x_3651_;
v___y_3558_ = v___y_3630_;
v___y_3559_ = v___y_3631_;
v___y_3560_ = v___x_3660_;
goto v___jp_3551_;
}
}
}
}
v___jp_3663_:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3664_, v___y_3668_, v___y_3665_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v_filterFn_3672_; uint8_t v_whitespace_3673_; uint8_t v_ordering_3674_; uint8_t v_reportPositions_3675_; uint8_t v_substring_3676_; lean_object* v___x_3677_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3670_);
v_filterFn_3672_ = lean_ctor_get(v_a_3671_, 0);
lean_inc_ref(v_filterFn_3672_);
v_whitespace_3673_ = lean_ctor_get_uint8(v_a_3671_, sizeof(void*)*1);
v_ordering_3674_ = lean_ctor_get_uint8(v_a_3671_, sizeof(void*)*1 + 1);
v_reportPositions_3675_ = lean_ctor_get_uint8(v_a_3671_, sizeof(void*)*1 + 2);
v_substring_3676_ = lean_ctor_get_uint8(v_a_3671_, sizeof(void*)*1 + 3);
lean_dec(v_a_3671_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3668_);
v___x_3677_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3666_, v___y_3668_, v___y_3665_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v_a_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v_str_3687_; lean_object* v_startInclusive_3688_; lean_object* v_endExclusive_3689_; lean_object* v_fst_3690_; lean_object* v_snd_3691_; lean_object* v_fileMap_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3677_);
v___x_3679_ = l_Lean_MessageLog_toList(v_a_3678_);
v___x_3680_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3681_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3672_, v___x_3679_, v___x_3680_);
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
v___x_3683_ = lean_unsigned_to_nat(0u);
v___x_3684_ = lean_string_utf8_byte_size(v___y_3669_);
v___x_3685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3685_, 0, v___y_3669_);
lean_ctor_set(v___x_3685_, 1, v___x_3683_);
lean_ctor_set(v___x_3685_, 2, v___x_3684_);
v___x_3686_ = l_String_Slice_trimAscii(v___x_3685_);
v_str_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc_ref(v_str_3687_);
v_startInclusive_3688_ = lean_ctor_get(v___x_3686_, 1);
lean_inc(v_startInclusive_3688_);
v_endExclusive_3689_ = lean_ctor_get(v___x_3686_, 2);
lean_inc(v_endExclusive_3689_);
lean_dec_ref(v___x_3686_);
v_fst_3690_ = lean_ctor_get(v_a_3682_, 0);
lean_inc(v_fst_3690_);
v_snd_3691_ = lean_ctor_get(v_a_3682_, 1);
lean_inc(v_snd_3691_);
lean_dec(v_a_3682_);
v_fileMap_3692_ = lean_ctor_get(v___y_3668_, 1);
v___x_3693_ = lean_string_utf8_extract(v_str_3687_, v_startInclusive_3688_, v_endExclusive_3689_);
lean_dec(v_endExclusive_3689_);
lean_dec(v_startInclusive_3688_);
lean_dec_ref(v_str_3687_);
v___x_3694_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3693_);
if (v_reportPositions_3675_ == 0)
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_box(0);
v___y_3623_ = v_whitespace_3673_;
v___y_3624_ = v_a_3678_;
v___y_3625_ = v___y_3665_;
v___y_3626_ = v_snd_3691_;
v___y_3627_ = v___x_3694_;
v___y_3628_ = v___x_3683_;
v___y_3629_ = v_substring_3676_;
v___y_3630_ = v___y_3667_;
v___y_3631_ = v___y_3668_;
v___y_3632_ = v_ordering_3674_;
v___y_3633_ = v_fst_3690_;
v___y_3634_ = v___x_3695_;
goto v___jp_3622_;
}
else
{
uint8_t v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = 0;
v___x_3697_ = l_Lean_Syntax_getPos_x3f(v___y_3667_, v___x_3696_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = lean_box(0);
v___y_3623_ = v_whitespace_3673_;
v___y_3624_ = v_a_3678_;
v___y_3625_ = v___y_3665_;
v___y_3626_ = v_snd_3691_;
v___y_3627_ = v___x_3694_;
v___y_3628_ = v___x_3683_;
v___y_3629_ = v_substring_3676_;
v___y_3630_ = v___y_3667_;
v___y_3631_ = v___y_3668_;
v___y_3632_ = v_ordering_3674_;
v___y_3633_ = v_fst_3690_;
v___y_3634_ = v___x_3698_;
goto v___jp_3622_;
}
else
{
lean_object* v_val_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3708_; 
v_val_3699_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3701_ = v___x_3697_;
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_val_3699_);
lean_dec(v___x_3697_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v_line_3704_; lean_object* v___x_3706_; 
lean_inc_ref(v_fileMap_3692_);
v___x_3703_ = l_Lean_FileMap_toPosition(v_fileMap_3692_, v_val_3699_);
lean_dec(v_val_3699_);
v_line_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_line_3704_);
lean_dec_ref(v___x_3703_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v_line_3704_);
v___x_3706_ = v___x_3701_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_line_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
v___y_3623_ = v_whitespace_3673_;
v___y_3624_ = v_a_3678_;
v___y_3625_ = v___y_3665_;
v___y_3626_ = v_snd_3691_;
v___y_3627_ = v___x_3694_;
v___y_3628_ = v___x_3683_;
v___y_3629_ = v_substring_3676_;
v___y_3630_ = v___y_3667_;
v___y_3631_ = v___y_3668_;
v___y_3632_ = v_ordering_3674_;
v___y_3633_ = v_fst_3690_;
v___y_3634_ = v___x_3706_;
goto v___jp_3622_;
}
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v_filterFn_3672_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec(v___y_3665_);
v_a_3709_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3677_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3677_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec(v___y_3665_);
v_a_3717_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3670_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3670_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
v___jp_3725_:
{
if (lean_obj_tag(v___y_3726_) == 0)
{
lean_object* v___x_3732_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3664_ = v___y_3731_;
v___y_3665_ = v___y_3727_;
v___y_3666_ = v___y_3728_;
v___y_3667_ = v___y_3729_;
v___y_3668_ = v___y_3730_;
v___y_3669_ = v___x_3732_;
goto v___jp_3663_;
}
else
{
lean_object* v_val_3733_; lean_object* v___x_3734_; 
v_val_3733_ = lean_ctor_get(v___y_3726_, 0);
lean_inc(v_val_3733_);
lean_dec_ref(v___y_3726_);
lean_inc_ref(v___y_3730_);
v___x_3734_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3733_, v___y_3730_, v___y_3727_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref(v___x_3734_);
v___y_3664_ = v___y_3731_;
v___y_3665_ = v___y_3727_;
v___y_3666_ = v___y_3728_;
v___y_3667_ = v___y_3729_;
v___y_3668_ = v___y_3730_;
v___y_3669_ = v_a_3735_;
goto v___jp_3663_;
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec(v___y_3727_);
v_a_3736_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3734_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3734_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
}
v___jp_3744_:
{
lean_object* v___x_3748_; lean_object* v_tk_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3748_ = lean_unsigned_to_nat(1u);
v_tk_3749_ = l_Lean_Syntax_getArg(v_x_3515_, v___x_3748_);
v___x_3750_ = lean_unsigned_to_nat(2u);
v___x_3751_ = l_Lean_Syntax_getArg(v_x_3515_, v___x_3750_);
v___x_3752_ = lean_unsigned_to_nat(4u);
v___x_3753_ = l_Lean_Syntax_getArg(v_x_3515_, v___x_3752_);
lean_dec(v_x_3515_);
v___x_3754_ = l_Lean_Syntax_getOptional_x3f(v___x_3751_);
lean_dec(v___x_3751_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_box(0);
v___y_3726_ = v_dc_x3f_3745_;
v___y_3727_ = v___y_3747_;
v___y_3728_ = v___x_3753_;
v___y_3729_ = v_tk_3749_;
v___y_3730_ = v___y_3746_;
v___y_3731_ = v___x_3755_;
goto v___jp_3725_;
}
else
{
lean_object* v_val_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_val_3756_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3754_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_val_3756_);
lean_dec(v___x_3754_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_val_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
v___y_3726_ = v_dc_x3f_3745_;
v___y_3727_ = v___y_3747_;
v___y_3728_ = v___x_3753_;
v___y_3729_ = v_tk_3749_;
v___y_3730_ = v___y_3746_;
v___y_3731_ = v___x_3761_;
goto v___jp_3725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3779_, v_a_3780_, v_a_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3784_, lean_object* v_as_3785_, lean_object* v_as_x27_3786_, lean_object* v_b_3787_, lean_object* v_a_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3784_, v_as_x27_3786_, v_b_3787_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3793_, lean_object* v_as_3794_, lean_object* v_as_x27_3795_, lean_object* v_b_3796_, lean_object* v_a_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3793_, v_as_3794_, v_as_x27_3795_, v_b_3796_, v_a_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v_as_3794_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3802_, lean_object* v_x_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3802_, v_x_3803_, v_x_3804_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3809_, v_x_3810_, v_x_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3809_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3816_, v___y_3818_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v_inst_3829_, lean_object* v_R_3830_, lean_object* v_a_3831_, lean_object* v_b_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3826_, v___x_3827_, v___x_3828_, v_a_3831_, v_b_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3834_, lean_object* v___x_3835_, lean_object* v___x_3836_, lean_object* v_inst_3837_, lean_object* v_R_3838_, lean_object* v_a_3839_, lean_object* v_b_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3834_, v___x_3835_, v___x_3836_, v_inst_3837_, v_R_3838_, v_a_3839_, v_b_3840_);
lean_dec_ref(v___x_3835_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3842_, v___y_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3852_, lean_object* v___x_3853_, lean_object* v___x_3854_, lean_object* v_inst_3855_, lean_object* v_R_3856_, lean_object* v_a_3857_, lean_object* v_b_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3852_, v___x_3853_, v___x_3854_, v_a_3857_, v_b_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3860_, lean_object* v___x_3861_, lean_object* v___x_3862_, lean_object* v_inst_3863_, lean_object* v_R_3864_, lean_object* v_a_3865_, lean_object* v_b_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3860_, v___x_3861_, v___x_3862_, v_inst_3863_, v_R_3864_, v_a_3865_, v_b_3866_);
lean_dec_ref(v___x_3861_);
return v_res_3867_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3868_, lean_object* v_inst_3869_, lean_object* v_R_3870_, lean_object* v_a_3871_, uint8_t v_b_3872_, lean_object* v_c_3873_){
_start:
{
uint8_t v___x_3874_; 
v___x_3874_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3868_, v_a_3871_, v_b_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3875_, lean_object* v_inst_3876_, lean_object* v_R_3877_, lean_object* v_a_3878_, lean_object* v_b_3879_, lean_object* v_c_3880_){
_start:
{
uint8_t v_b_boxed_3881_; uint8_t v_res_3882_; lean_object* v_r_3883_; 
v_b_boxed_3881_ = lean_unbox(v_b_3879_);
v_res_3882_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3875_, v_inst_3876_, v_R_3877_, v_a_3878_, v_b_boxed_3881_, v_c_3880_);
lean_dec_ref(v_s_3875_);
v_r_3883_ = lean_box(v_res_3882_);
return v_r_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3884_, lean_object* v_ref_3885_, lean_object* v_msg_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3885_, v_msg_3886_, v___y_3887_, v___y_3888_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3891_, lean_object* v_ref_3892_, lean_object* v_msg_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3891_, v_ref_3892_, v_msg_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec(v_ref_3892_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3898_, lean_object* v_as_x27_3899_, lean_object* v_b_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3899_, v_b_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3903_, lean_object* v_as_x27_3904_, lean_object* v_b_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3903_, v_as_x27_3904_, v_b_3905_, v_a_3906_);
lean_dec(v_as_3903_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3908_, lean_object* v_rsize_3909_, lean_object* v_histogram_3910_, lean_object* v_index_3911_, lean_object* v_val_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3910_, v_index_3911_, v_val_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3914_, lean_object* v_rsize_3915_, lean_object* v_histogram_3916_, lean_object* v_index_3917_, lean_object* v_val_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3914_, v_rsize_3915_, v_histogram_3916_, v_index_3917_, v_val_3918_);
lean_dec(v_rsize_3915_);
lean_dec(v_lsize_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3920_, lean_object* v___x_3921_, lean_object* v_fst_3922_, lean_object* v___x_3923_, lean_object* v_inst_3924_, lean_object* v_R_3925_, lean_object* v_a_3926_, lean_object* v_b_3927_, lean_object* v_c_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3920_, v___x_3921_, v_fst_3922_, v___x_3923_, v_a_3926_, v_b_3927_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3930_, lean_object* v___x_3931_, lean_object* v_fst_3932_, lean_object* v___x_3933_, lean_object* v_inst_3934_, lean_object* v_R_3935_, lean_object* v_a_3936_, lean_object* v_b_3937_, lean_object* v_c_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3930_, v___x_3931_, v_fst_3932_, v___x_3933_, v_inst_3934_, v_R_3935_, v_a_3936_, v_b_3937_, v_c_3938_);
lean_dec(v___x_3933_);
lean_dec_ref(v_fst_3932_);
lean_dec(v___x_3931_);
lean_dec(v_upperBound_3930_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_3940_, lean_object* v_rsize_3941_, lean_object* v_histogram_3942_, lean_object* v_index_3943_, lean_object* v_val_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_3942_, v_index_3943_, v_val_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_3946_, lean_object* v_rsize_3947_, lean_object* v_histogram_3948_, lean_object* v_index_3949_, lean_object* v_val_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_3946_, v_rsize_3947_, v_histogram_3948_, v_index_3949_, v_val_3950_);
lean_dec(v_rsize_3947_);
lean_dec(v_lsize_3946_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_3952_, lean_object* v_fst_3953_, lean_object* v___x_3954_, lean_object* v_fst_3955_, lean_object* v_inst_3956_, lean_object* v_R_3957_, lean_object* v_a_3958_, lean_object* v_b_3959_, lean_object* v_c_3960_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3952_, v_fst_3953_, v___x_3954_, v_fst_3955_, v_a_3958_, v_b_3959_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_3962_, lean_object* v_fst_3963_, lean_object* v___x_3964_, lean_object* v_fst_3965_, lean_object* v_inst_3966_, lean_object* v_R_3967_, lean_object* v_a_3968_, lean_object* v_b_3969_, lean_object* v_c_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_3962_, v_fst_3963_, v___x_3964_, v_fst_3965_, v_inst_3966_, v_R_3967_, v_a_3968_, v_b_3969_, v_c_3970_);
lean_dec_ref(v_fst_3965_);
lean_dec(v___x_3964_);
lean_dec_ref(v_fst_3963_);
lean_dec(v_upperBound_3962_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_3972_, lean_object* v_msg_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_3973_, v___y_3974_, v___y_3975_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_3978_, lean_object* v_msg_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_3978_, v_msg_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_3984_, lean_object* v_m_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_3985_, v_a_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_3988_, lean_object* v_m_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_3988_, v_m_3989_, v_a_3990_);
lean_dec_ref(v_a_3990_);
lean_dec_ref(v_m_3989_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_3992_, lean_object* v_m_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_3993_, v_a_3994_, v_b_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_3997_, lean_object* v_macroStack_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_3997_, v_macroStack_3998_, v___y_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4003_, lean_object* v_macroStack_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4003_, v_macroStack_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4009_, lean_object* v_R_4010_, lean_object* v_a_4011_, lean_object* v_b_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4011_, v_b_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4014_, lean_object* v_a_4015_, lean_object* v_x_4016_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4015_, v_x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4018_, lean_object* v_a_4019_, lean_object* v_x_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4018_, v_a_4019_, v_x_4020_);
lean_dec(v_x_4020_);
lean_dec_ref(v_a_4019_);
return v_res_4021_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4022_, lean_object* v_a_4023_, lean_object* v_x_4024_){
_start:
{
uint8_t v___x_4025_; 
v___x_4025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4023_, v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4026_, lean_object* v_a_4027_, lean_object* v_x_4028_){
_start:
{
uint8_t v_res_4029_; lean_object* v_r_4030_; 
v_res_4029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4026_, v_a_4027_, v_x_4028_);
lean_dec(v_x_4028_);
lean_dec_ref(v_a_4027_);
v_r_4030_ = lean_box(v_res_4029_);
return v_r_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4031_, lean_object* v_data_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4034_, lean_object* v_a_4035_, lean_object* v_b_4036_, lean_object* v_x_4037_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4035_, v_b_4036_, v_x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4039_, lean_object* v_i_4040_, lean_object* v_source_4041_, lean_object* v_target_4042_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4040_, v_source_4041_, v_target_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4044_, lean_object* v_x_4045_, lean_object* v_x_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4045_, v_x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4056_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4057_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4058_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4059_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4060_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4056_, v___x_4057_, v___x_4058_, v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4090_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4091_ = l_Lean_addBuiltinDeclarationRanges(v___x_4089_, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4094_){
_start:
{
lean_object* v_doc_4096_; lean_object* v___x_4097_; 
v_doc_4096_ = lean_ctor_get(v___y_4094_, 1);
lean_inc_ref(v_doc_4096_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_doc_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4098_);
lean_dec_ref(v___y_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4101_, lean_object* v_a_4102_, uint8_t v_b_4103_){
_start:
{
lean_object* v_str_4104_; lean_object* v_startInclusive_4105_; lean_object* v_endExclusive_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v_str_4104_ = lean_ctor_get(v_s_4101_, 0);
v_startInclusive_4105_ = lean_ctor_get(v_s_4101_, 1);
v_endExclusive_4106_ = lean_ctor_get(v_s_4101_, 2);
v___x_4107_ = lean_nat_sub(v_endExclusive_4106_, v_startInclusive_4105_);
v___x_4108_ = lean_nat_dec_eq(v_a_4102_, v___x_4107_);
lean_dec(v___x_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; uint32_t v___x_4110_; uint32_t v___x_4111_; uint8_t v___x_4112_; 
v___x_4109_ = lean_nat_add(v_startInclusive_4105_, v_a_4102_);
lean_dec(v_a_4102_);
v___x_4110_ = lean_string_utf8_get_fast(v_str_4104_, v___x_4109_);
v___x_4111_ = 10;
v___x_4112_ = lean_uint32_dec_eq(v___x_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_string_utf8_next_fast(v_str_4104_, v___x_4109_);
lean_dec(v___x_4109_);
v___x_4114_ = lean_nat_sub(v___x_4113_, v_startInclusive_4105_);
v_a_4102_ = v___x_4114_;
v_b_4103_ = v___x_4112_;
goto _start;
}
else
{
lean_dec(v___x_4109_);
return v___x_4112_;
}
}
else
{
lean_dec(v_a_4102_);
return v_b_4103_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4116_, lean_object* v_a_4117_, lean_object* v_b_4118_){
_start:
{
uint8_t v_b_boxed_4119_; uint8_t v_res_4120_; lean_object* v_r_4121_; 
v_b_boxed_4119_ = lean_unbox(v_b_4118_);
v_res_4120_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4116_, v_a_4117_, v_b_boxed_4119_);
lean_dec_ref(v_s_4116_);
v_r_4121_ = lean_box(v_res_4120_);
return v_r_4121_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4122_){
_start:
{
lean_object* v_searcher_4123_; uint8_t v___x_4124_; uint8_t v___x_4125_; 
v_searcher_4123_ = lean_unsigned_to_nat(0u);
v___x_4124_ = 0;
v___x_4125_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4122_, v_searcher_4123_, v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4126_){
_start:
{
uint8_t v_res_4127_; lean_object* v_r_4128_; 
v_res_4127_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4126_);
lean_dec_ref(v_s_4126_);
v_r_4128_ = lean_box(v_res_4127_);
return v_r_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4140_, lean_object* v_fst_4141_, uint8_t v___x_4142_, lean_object* v_a_4143_, lean_object* v___x_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v___x_4147_, lean_object* v___x_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v___x_4151_, lean_object* v_snd_4152_, lean_object* v___x_4153_){
_start:
{
if (lean_obj_tag(v___x_4140_) == 1)
{
lean_object* v_val_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4218_; 
v_val_4155_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4157_ = v___x_4140_;
v_isShared_4158_ = v_isSharedCheck_4218_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_val_4155_);
lean_dec(v___x_4140_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4218_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4161_ = l_Lean_Syntax_setArg(v_fst_4141_, v___x_4159_, v___x_4160_);
v___x_4162_ = l_Lean_Syntax_getPos_x3f(v___x_4161_, v___x_4142_);
lean_dec(v___x_4161_);
if (lean_obj_tag(v___x_4162_) == 1)
{
lean_object* v_val_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v___x_4153_);
v_val_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4214_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_val_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4214_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___y_4168_; lean_object* v___x_4194_; uint8_t v___y_4201_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4194_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4152_);
v___x_4206_ = lean_string_utf8_byte_size(v___x_4194_);
v___x_4207_ = lean_nat_dec_eq(v___x_4206_, v___x_4159_);
if (v___x_4207_ == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4208_ = lean_string_length(v___x_4194_);
v___x_4209_ = lean_unsigned_to_nat(93u);
v___x_4210_ = lean_nat_dec_le(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
v___y_4201_ = v___x_4210_;
goto v___jp_4200_;
}
else
{
lean_object* v___x_4211_; uint8_t v___x_4212_; 
lean_inc_ref(v___x_4194_);
v___x_4211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4194_);
lean_ctor_set(v___x_4211_, 1, v___x_4159_);
lean_ctor_set(v___x_4211_, 2, v___x_4206_);
v___x_4212_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4211_);
lean_dec_ref(v___x_4211_);
if (v___x_4212_ == 0)
{
v___y_4201_ = v___x_4210_;
goto v___jp_4200_;
}
else
{
goto v___jp_4195_;
}
}
}
else
{
lean_object* v___x_4213_; 
lean_dec_ref(v___x_4194_);
v___x_4213_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4168_ = v___x_4213_;
goto v___jp_4167_;
}
v___jp_4167_:
{
lean_object* v_toEditableDocumentCore_4169_; lean_object* v_meta_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4190_; 
v_toEditableDocumentCore_4169_ = lean_ctor_get(v_a_4143_, 0);
lean_inc_ref(v_toEditableDocumentCore_4169_);
v_meta_4170_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_toEditableDocumentCore_4169_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; lean_object* v_unused_4192_; lean_object* v_unused_4193_; 
v_unused_4191_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 3);
lean_dec(v_unused_4191_);
v_unused_4192_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 2);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 1);
lean_dec(v_unused_4193_);
v___x_4172_ = v_toEditableDocumentCore_4169_;
v_isShared_4173_ = v_isSharedCheck_4190_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_meta_4170_);
lean_dec(v_toEditableDocumentCore_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4190_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v_text_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v_text_4174_ = lean_ctor_get(v_meta_4170_, 3);
lean_inc_ref(v_text_4174_);
lean_dec_ref(v_meta_4170_);
v___x_4175_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4143_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_val_4155_);
lean_ctor_set(v___x_4176_, 1, v_val_4163_);
v___x_4177_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4174_, v___x_4176_);
v___x_4178_ = lean_box(0);
lean_inc(v___x_4144_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 3, v___x_4144_);
lean_ctor_set(v___x_4172_, 2, v___x_4178_);
lean_ctor_set(v___x_4172_, 1, v___y_4168_);
lean_ctor_set(v___x_4172_, 0, v___x_4177_);
v___x_4180_ = v___x_4172_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v___y_4168_);
lean_ctor_set(v_reuseFailAlloc_4189_, 2, v___x_4178_);
lean_ctor_set(v_reuseFailAlloc_4189_, 3, v___x_4144_);
v___x_4180_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4181_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4175_, v___x_4180_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4181_);
v___x_4183_ = v___x_4165_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4186_; 
lean_inc(v___x_4144_);
v___x_4184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4144_);
lean_ctor_set(v___x_4184_, 1, v___x_4144_);
lean_ctor_set(v___x_4184_, 2, v___x_4145_);
lean_ctor_set(v___x_4184_, 3, v___x_4146_);
lean_ctor_set(v___x_4184_, 4, v___x_4147_);
lean_ctor_set(v___x_4184_, 5, v___x_4148_);
lean_ctor_set(v___x_4184_, 6, v___x_4149_);
lean_ctor_set(v___x_4184_, 7, v___x_4183_);
lean_ctor_set(v___x_4184_, 8, v___x_4150_);
lean_ctor_set(v___x_4184_, 9, v___x_4151_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4184_);
v___x_4186_ = v___x_4157_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
v___jp_4195_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4197_ = lean_string_append(v___x_4196_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4198_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4199_ = lean_string_append(v___x_4197_, v___x_4198_);
v___y_4168_ = v___x_4199_;
goto v___jp_4167_;
}
v___jp_4200_:
{
if (v___y_4201_ == 0)
{
goto v___jp_4195_;
}
else
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4202_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4203_ = lean_string_append(v___x_4202_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4204_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4205_ = lean_string_append(v___x_4203_, v___x_4204_);
v___y_4168_ = v___x_4205_;
goto v___jp_4167_;
}
}
}
}
else
{
lean_object* v___x_4216_; 
lean_dec(v___x_4162_);
lean_dec(v_val_4155_);
lean_dec_ref(v_snd_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec(v___x_4146_);
lean_dec_ref(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec_ref(v_a_4143_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4153_);
v___x_4216_ = v___x_4157_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4153_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v___x_4219_; 
lean_dec_ref(v_snd_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec(v___x_4146_);
lean_dec_ref(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_fst_4141_);
lean_dec(v___x_4140_);
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4153_);
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4220_, lean_object* v_fst_4221_, lean_object* v___x_4222_, lean_object* v_a_4223_, lean_object* v___x_4224_, lean_object* v___x_4225_, lean_object* v___x_4226_, lean_object* v___x_4227_, lean_object* v___x_4228_, lean_object* v___x_4229_, lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v_snd_4232_, lean_object* v___x_4233_, lean_object* v___y_4234_){
_start:
{
uint8_t v___x_5313__boxed_4235_; lean_object* v_res_4236_; 
v___x_5313__boxed_4235_ = lean_unbox(v___x_4222_);
v_res_4236_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4220_, v_fst_4221_, v___x_5313__boxed_4235_, v_a_4223_, v___x_4224_, v___x_4225_, v___x_4226_, v___x_4227_, v___x_4228_, v___x_4229_, v___x_4230_, v___x_4231_, v_snd_4232_, v___x_4233_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4240_, size_t v_sz_4241_, size_t v_i_4242_, lean_object* v_b_4243_){
_start:
{
lean_object* v_a_4245_; uint8_t v___x_4249_; 
v___x_4249_ = lean_usize_dec_lt(v_i_4242_, v_sz_4241_);
if (v___x_4249_ == 0)
{
return v_b_4243_;
}
else
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v_a_4252_; 
lean_dec_ref(v_b_4243_);
v___x_4250_ = lean_box(0);
v___x_4251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4252_ = lean_array_uget(v_as_4240_, v_i_4242_);
if (lean_obj_tag(v_a_4252_) == 1)
{
lean_object* v_i_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4287_; 
v_i_4253_ = lean_ctor_get(v_a_4252_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_a_4252_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; 
v_unused_4288_ = lean_ctor_get(v_a_4252_, 1);
lean_dec(v_unused_4288_);
v___x_4255_ = v_a_4252_;
v_isShared_4256_ = v_isSharedCheck_4287_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_i_4253_);
lean_dec(v_a_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4287_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
if (lean_obj_tag(v_i_4253_) == 10)
{
lean_object* v_i_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4286_; 
v_i_4257_ = lean_ctor_get(v_i_4253_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_i_4253_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4259_ = v_i_4253_;
v_isShared_4260_ = v_isSharedCheck_4286_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_i_4257_);
lean_dec(v_i_4253_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4286_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v_stx_4261_; lean_object* v_value_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4285_; 
v_stx_4261_ = lean_ctor_get(v_i_4257_, 0);
v_value_4262_ = lean_ctor_get(v_i_4257_, 1);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_i_4257_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4264_ = v_i_4257_;
v_isShared_4265_ = v_isSharedCheck_4285_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_value_4262_);
lean_inc(v_stx_4261_);
lean_dec(v_i_4257_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4285_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4267_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4262_, v___x_4266_);
lean_dec(v_value_4262_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_del_object(v___x_4264_);
lean_dec(v_stx_4261_);
lean_del_object(v___x_4259_);
lean_del_object(v___x_4255_);
v_a_4245_ = v___x_4251_;
goto v___jp_4244_;
}
else
{
lean_object* v_val_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4284_; 
v_val_4268_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4270_ = v___x_4267_;
v_isShared_4271_ = v_isSharedCheck_4284_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_val_4268_);
lean_dec(v___x_4267_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4284_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 1, v_val_4268_);
v___x_4273_ = v___x_4264_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_stx_4261_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v_val_4268_);
v___x_4273_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v___x_4275_; 
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 0, v___x_4273_);
v___x_4275_ = v___x_4270_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4277_; 
if (v_isShared_4260_ == 0)
{
lean_ctor_set_tag(v___x_4259_, 1);
lean_ctor_set(v___x_4259_, 0, v___x_4275_);
v___x_4277_ = v___x_4259_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
lean_object* v___x_4279_; 
if (v_isShared_4256_ == 0)
{
lean_ctor_set_tag(v___x_4255_, 0);
lean_ctor_set(v___x_4255_, 1, v___x_4250_);
lean_ctor_set(v___x_4255_, 0, v___x_4277_);
v___x_4279_ = v___x_4255_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4277_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v___x_4250_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
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
lean_del_object(v___x_4255_);
lean_dec_ref(v_i_4253_);
v_a_4245_ = v___x_4251_;
goto v___jp_4244_;
}
}
}
else
{
lean_dec(v_a_4252_);
v_a_4245_ = v___x_4251_;
goto v___jp_4244_;
}
}
v___jp_4244_:
{
size_t v___x_4246_; size_t v___x_4247_; 
v___x_4246_ = ((size_t)1ULL);
v___x_4247_ = lean_usize_add(v_i_4242_, v___x_4246_);
v_i_4242_ = v___x_4247_;
v_b_4243_ = v_a_4245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4289_, lean_object* v_sz_4290_, lean_object* v_i_4291_, lean_object* v_b_4292_){
_start:
{
size_t v_sz_boxed_4293_; size_t v_i_boxed_4294_; lean_object* v_res_4295_; 
v_sz_boxed_4293_ = lean_unbox_usize(v_sz_4290_);
lean_dec(v_sz_4290_);
v_i_boxed_4294_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4289_, v_sz_boxed_4293_, v_i_boxed_4294_, v_b_4292_);
lean_dec_ref(v_as_4289_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4296_, size_t v_sz_4297_, size_t v_i_4298_, lean_object* v_b_4299_){
_start:
{
lean_object* v_a_4301_; uint8_t v___x_4305_; 
v___x_4305_ = lean_usize_dec_lt(v_i_4298_, v_sz_4297_);
if (v___x_4305_ == 0)
{
lean_inc_ref(v_b_4299_);
return v_b_4299_;
}
else
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v_a_4308_; 
v___x_4306_ = lean_box(0);
v___x_4307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4308_ = lean_array_uget(v_as_4296_, v_i_4298_);
if (lean_obj_tag(v_a_4308_) == 1)
{
lean_object* v_i_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4343_; 
v_i_4309_ = lean_ctor_get(v_a_4308_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_a_4308_);
if (v_isSharedCheck_4343_ == 0)
{
lean_object* v_unused_4344_; 
v_unused_4344_ = lean_ctor_get(v_a_4308_, 1);
lean_dec(v_unused_4344_);
v___x_4311_ = v_a_4308_;
v_isShared_4312_ = v_isSharedCheck_4343_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_i_4309_);
lean_dec(v_a_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4343_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
if (lean_obj_tag(v_i_4309_) == 10)
{
lean_object* v_i_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4342_; 
v_i_4313_ = lean_ctor_get(v_i_4309_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_i_4309_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4315_ = v_i_4309_;
v_isShared_4316_ = v_isSharedCheck_4342_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_i_4313_);
lean_dec(v_i_4309_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4342_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v_stx_4317_; lean_object* v_value_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4341_; 
v_stx_4317_ = lean_ctor_get(v_i_4313_, 0);
v_value_4318_ = lean_ctor_get(v_i_4313_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_i_4313_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4320_ = v_i_4313_;
v_isShared_4321_ = v_isSharedCheck_4341_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_value_4318_);
lean_inc(v_stx_4317_);
lean_dec(v_i_4313_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4341_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4323_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4318_, v___x_4322_);
lean_dec(v_value_4318_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_del_object(v___x_4320_);
lean_dec(v_stx_4317_);
lean_del_object(v___x_4315_);
lean_del_object(v___x_4311_);
v_a_4301_ = v___x_4307_;
goto v___jp_4300_;
}
else
{
lean_object* v_val_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4340_; 
v_val_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4340_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_val_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4340_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 1, v_val_4324_);
v___x_4329_ = v___x_4320_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_stx_4317_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_val_4324_);
v___x_4329_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4331_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4329_);
v___x_4331_ = v___x_4326_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
lean_object* v___x_4333_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set_tag(v___x_4315_, 1);
lean_ctor_set(v___x_4315_, 0, v___x_4331_);
v___x_4333_ = v___x_4315_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4335_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 0);
lean_ctor_set(v___x_4311_, 1, v___x_4306_);
lean_ctor_set(v___x_4311_, 0, v___x_4333_);
v___x_4335_ = v___x_4311_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4336_, 1, v___x_4306_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
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
lean_del_object(v___x_4311_);
lean_dec_ref(v_i_4309_);
v_a_4301_ = v___x_4307_;
goto v___jp_4300_;
}
}
}
else
{
lean_dec(v_a_4308_);
v_a_4301_ = v___x_4307_;
goto v___jp_4300_;
}
}
v___jp_4300_:
{
size_t v___x_4302_; size_t v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = ((size_t)1ULL);
v___x_4303_ = lean_usize_add(v_i_4298_, v___x_4302_);
v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4296_, v_sz_4297_, v___x_4303_, v_a_4301_);
return v___x_4304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4345_, lean_object* v_sz_4346_, lean_object* v_i_4347_, lean_object* v_b_4348_){
_start:
{
size_t v_sz_boxed_4349_; size_t v_i_boxed_4350_; lean_object* v_res_4351_; 
v_sz_boxed_4349_ = lean_unbox_usize(v_sz_4346_);
lean_dec(v_sz_4346_);
v_i_boxed_4350_ = lean_unbox_usize(v_i_4347_);
lean_dec(v_i_4347_);
v_res_4351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4345_, v_sz_boxed_4349_, v_i_boxed_4350_, v_b_4348_);
lean_dec_ref(v_b_4348_);
lean_dec_ref(v_as_4345_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4352_){
_start:
{
if (lean_obj_tag(v_x_4352_) == 0)
{
lean_object* v_cs_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; size_t v_sz_4356_; size_t v___x_4357_; lean_object* v___x_4358_; lean_object* v_fst_4359_; 
v_cs_4353_ = lean_ctor_get(v_x_4352_, 0);
v___x_4354_ = lean_box(0);
v___x_4355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4356_ = lean_array_size(v_cs_4353_);
v___x_4357_ = ((size_t)0ULL);
v___x_4358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4353_, v_sz_4356_, v___x_4357_, v___x_4355_);
v_fst_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_fst_4359_);
lean_dec_ref(v___x_4358_);
if (lean_obj_tag(v_fst_4359_) == 0)
{
return v___x_4354_;
}
else
{
lean_object* v_val_4360_; 
v_val_4360_ = lean_ctor_get(v_fst_4359_, 0);
lean_inc(v_val_4360_);
lean_dec_ref(v_fst_4359_);
return v_val_4360_;
}
}
else
{
lean_object* v_vs_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; size_t v_sz_4364_; size_t v___x_4365_; lean_object* v___x_4366_; lean_object* v_fst_4367_; 
v_vs_4361_ = lean_ctor_get(v_x_4352_, 0);
v___x_4362_ = lean_box(0);
v___x_4363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4364_ = lean_array_size(v_vs_4361_);
v___x_4365_ = ((size_t)0ULL);
v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4361_, v_sz_4364_, v___x_4365_, v___x_4363_);
v_fst_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_fst_4367_);
lean_dec_ref(v___x_4366_);
if (lean_obj_tag(v_fst_4367_) == 0)
{
return v___x_4362_;
}
else
{
lean_object* v_val_4368_; 
v_val_4368_ = lean_ctor_get(v_fst_4367_, 0);
lean_inc(v_val_4368_);
lean_dec_ref(v_fst_4367_);
return v_val_4368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4369_, size_t v_sz_4370_, size_t v_i_4371_, lean_object* v_b_4372_){
_start:
{
uint8_t v___x_4373_; 
v___x_4373_ = lean_usize_dec_lt(v_i_4371_, v_sz_4370_);
if (v___x_4373_ == 0)
{
return v_b_4372_;
}
else
{
lean_object* v___x_4374_; lean_object* v_a_4375_; lean_object* v___x_4376_; 
lean_dec_ref(v_b_4372_);
v___x_4374_ = lean_box(0);
v_a_4375_ = lean_array_uget_borrowed(v_as_4369_, v_i_4371_);
v___x_4376_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4375_);
if (lean_obj_tag(v___x_4376_) == 1)
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
lean_ctor_set(v___x_4378_, 1, v___x_4374_);
return v___x_4378_;
}
else
{
lean_object* v___x_4379_; size_t v___x_4380_; size_t v___x_4381_; 
lean_dec(v___x_4376_);
v___x_4379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4380_ = ((size_t)1ULL);
v___x_4381_ = lean_usize_add(v_i_4371_, v___x_4380_);
v_i_4371_ = v___x_4381_;
v_b_4372_ = v___x_4379_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4383_, lean_object* v_sz_4384_, lean_object* v_i_4385_, lean_object* v_b_4386_){
_start:
{
size_t v_sz_boxed_4387_; size_t v_i_boxed_4388_; lean_object* v_res_4389_; 
v_sz_boxed_4387_ = lean_unbox_usize(v_sz_4384_);
lean_dec(v_sz_4384_);
v_i_boxed_4388_ = lean_unbox_usize(v_i_4385_);
lean_dec(v_i_4385_);
v_res_4389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4383_, v_sz_boxed_4387_, v_i_boxed_4388_, v_b_4386_);
lean_dec_ref(v_as_4383_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4390_);
lean_dec_ref(v_x_4390_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4392_){
_start:
{
lean_object* v_root_4393_; lean_object* v_tail_4394_; lean_object* v___x_4395_; 
v_root_4393_ = lean_ctor_get(v_t_4392_, 0);
v_tail_4394_ = lean_ctor_get(v_t_4392_, 1);
v___x_4395_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4393_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v___x_4396_; size_t v_sz_4397_; size_t v___x_4398_; lean_object* v___x_4399_; lean_object* v_fst_4400_; 
v___x_4396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4397_ = lean_array_size(v_tail_4394_);
v___x_4398_ = ((size_t)0ULL);
v___x_4399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4394_, v_sz_4397_, v___x_4398_, v___x_4396_);
v_fst_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_fst_4400_);
lean_dec_ref(v___x_4399_);
if (lean_obj_tag(v_fst_4400_) == 0)
{
return v___x_4395_;
}
else
{
lean_object* v_val_4401_; 
v_val_4401_ = lean_ctor_get(v_fst_4400_, 0);
lean_inc(v_val_4401_);
lean_dec_ref(v_fst_4400_);
return v_val_4401_;
}
}
else
{
return v___x_4395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4402_);
lean_dec_ref(v_t_4402_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4418_, lean_object* v_a_4419_){
_start:
{
if (lean_obj_tag(v_node_4418_) == 1)
{
lean_object* v_children_4421_; lean_object* v_res_4422_; 
v_children_4421_ = lean_ctor_get(v_node_4418_, 1);
v_res_4422_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4421_);
if (lean_obj_tag(v_res_4422_) == 1)
{
lean_object* v_val_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4460_; 
v_val_4423_ = lean_ctor_get(v_res_4422_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_res_4422_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4425_ = v_res_4422_;
v_isShared_4426_ = v_isSharedCheck_4460_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_val_4423_);
lean_dec(v_res_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4460_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v_fst_4427_; lean_object* v_snd_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4459_; 
v_fst_4427_ = lean_ctor_get(v_val_4423_, 0);
v_snd_4428_ = lean_ctor_get(v_val_4423_, 1);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_val_4423_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4430_ = v_val_4423_;
v_isShared_4431_ = v_isSharedCheck_4459_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_snd_4428_);
lean_inc(v_fst_4427_);
lean_dec(v_val_4423_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4459_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4458_; 
v___x_4432_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4419_);
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4458_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4458_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; uint8_t v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___y_4445_; lean_object* v___x_4447_; 
v___x_4437_ = lean_box(0);
v___x_4438_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4439_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4440_ = 1;
v___x_4441_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4442_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4443_ = l_Lean_Syntax_getPos_x3f(v_fst_4427_, v___x_4440_);
v___x_4444_ = lean_box(v___x_4440_);
v___y_4445_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4445_, 0, v___x_4443_);
lean_closure_set(v___y_4445_, 1, v_fst_4427_);
lean_closure_set(v___y_4445_, 2, v___x_4444_);
lean_closure_set(v___y_4445_, 3, v_a_4433_);
lean_closure_set(v___y_4445_, 4, v___x_4437_);
lean_closure_set(v___y_4445_, 5, v___x_4438_);
lean_closure_set(v___y_4445_, 6, v___x_4439_);
lean_closure_set(v___y_4445_, 7, v___x_4437_);
lean_closure_set(v___y_4445_, 8, v___x_4441_);
lean_closure_set(v___y_4445_, 9, v___x_4437_);
lean_closure_set(v___y_4445_, 10, v___x_4437_);
lean_closure_set(v___y_4445_, 11, v___x_4437_);
lean_closure_set(v___y_4445_, 12, v_snd_4428_);
lean_closure_set(v___y_4445_, 13, v___x_4442_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___y_4445_);
v___x_4447_ = v___x_4425_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___y_4445_);
v___x_4447_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4449_; 
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 1, v___x_4447_);
lean_ctor_set(v___x_4430_, 0, v___x_4442_);
v___x_4449_ = v___x_4430_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4442_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4454_; 
v___x_4450_ = lean_unsigned_to_nat(1u);
v___x_4451_ = lean_mk_empty_array_with_capacity(v___x_4450_);
v___x_4452_ = lean_array_push(v___x_4451_, v___x_4449_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4452_);
v___x_4454_ = v___x_4435_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
lean_dec(v_res_4422_);
v___x_4461_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4465_, v_a_4466_);
lean_dec_ref(v_a_4466_);
lean_dec_ref(v_node_4465_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4469_, lean_object* v_x_4470_, lean_object* v_x_4471_, lean_object* v_node_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4472_, v_a_4473_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4476_, lean_object* v_x_4477_, lean_object* v_x_4478_, lean_object* v_node_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4476_, v_x_4477_, v_x_4478_, v_node_4479_, v_a_4480_);
lean_dec_ref(v_a_4480_);
lean_dec_ref(v_node_4479_);
lean_dec_ref(v_x_4478_);
lean_dec_ref(v_x_4477_);
lean_dec_ref(v_x_4476_);
return v_res_4482_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4483_, lean_object* v_inst_4484_, lean_object* v_R_4485_, lean_object* v_a_4486_, uint8_t v_b_4487_, lean_object* v_c_4488_){
_start:
{
uint8_t v___x_4489_; 
v___x_4489_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4483_, v_a_4486_, v_b_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4490_, lean_object* v_inst_4491_, lean_object* v_R_4492_, lean_object* v_a_4493_, lean_object* v_b_4494_, lean_object* v_c_4495_){
_start:
{
uint8_t v_b_boxed_4496_; uint8_t v_res_4497_; lean_object* v_r_4498_; 
v_b_boxed_4496_ = lean_unbox(v_b_4494_);
v_res_4497_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4490_, v_inst_4491_, v_R_4492_, v_a_4493_, v_b_boxed_4496_, v_c_4495_);
lean_dec_ref(v_s_4490_);
v_r_4498_ = lean_box(v_res_4497_);
return v_r_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_(){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_));
v___x_4505_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4506_ = l_Lean_CodeAction_insertBuiltin(v___x_4504_, v___x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369____boxed(lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
return v_res_4508_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4511_ = lean_string_utf8_byte_size(v___x_4510_);
return v___x_4511_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4512_ = lean_unsigned_to_nat(0u);
v___x_4513_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4514_ = lean_nat_dec_eq(v___x_4513_, v___x_4512_);
return v___x_4514_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4515_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4516_ = lean_unsigned_to_nat(0u);
v___x_4517_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v___x_4516_);
lean_ctor_set(v___x_4518_, 2, v___x_4515_);
return v___x_4518_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4520_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4519_);
return v___x_4520_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4521_ = lean_unsigned_to_nat(0u);
v___x_4522_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4523_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4524_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
lean_ctor_set(v___x_4524_, 1, v___x_4522_);
lean_ctor_set(v___x_4524_, 2, v___x_4521_);
lean_ctor_set(v___x_4524_, 3, v___x_4521_);
return v___x_4524_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4525_){
_start:
{
lean_object* v___y_4527_; uint8_t v___x_4530_; 
v___x_4530_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4527_ = v___x_4531_;
goto v___jp_4526_;
}
else
{
lean_object* v___x_4532_; 
v___x_4532_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4527_ = v___x_4532_;
goto v___jp_4526_;
}
v___jp_4526_:
{
uint8_t v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = 0;
v___x_4529_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4525_, v___y_4527_, v___x_4528_);
return v___x_4529_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4533_){
_start:
{
uint8_t v_res_4534_; lean_object* v_r_4535_; 
v_res_4534_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4533_);
lean_dec_ref(v_s_4533_);
v_r_4535_ = lean_box(v_res_4534_);
return v_r_4535_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4536_, lean_object* v_as_x27_4537_, uint8_t v_b_4538_){
_start:
{
if (lean_obj_tag(v_as_x27_4537_) == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = lean_box(v_b_4538_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
return v___x_4541_;
}
else
{
lean_object* v_head_4542_; uint8_t v_isSilent_4543_; 
v_head_4542_ = lean_ctor_get(v_as_x27_4537_, 0);
v_isSilent_4543_ = lean_ctor_get_uint8(v_head_4542_, sizeof(void*)*5 + 2);
if (v_isSilent_4543_ == 0)
{
lean_object* v_tail_4544_; lean_object* v_data_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
lean_inc(v_head_4542_);
v_tail_4544_ = lean_ctor_get(v_as_x27_4537_, 1);
lean_inc(v_tail_4544_);
lean_dec_ref(v_as_x27_4537_);
v_data_4545_ = lean_ctor_get(v_head_4542_, 4);
lean_inc(v_data_4545_);
lean_dec(v_head_4542_);
v___x_4546_ = l_Lean_MessageData_toString(v_data_4545_);
v___x_4547_ = lean_unsigned_to_nat(0u);
v___x_4548_ = lean_string_utf8_byte_size(v___x_4546_);
v___x_4549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4546_);
lean_ctor_set(v___x_4549_, 1, v___x_4547_);
lean_ctor_set(v___x_4549_, 2, v___x_4548_);
v___x_4550_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4549_);
lean_dec_ref(v___x_4549_);
if (v___x_4550_ == 0)
{
v_as_x27_4537_ = v_tail_4544_;
goto _start;
}
else
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v_tail_4544_);
v___x_4552_ = lean_box(v_foundPanic_4536_);
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
}
else
{
lean_object* v_tail_4554_; 
v_tail_4554_ = lean_ctor_get(v_as_x27_4537_, 1);
lean_inc(v_tail_4554_);
lean_dec_ref(v_as_x27_4537_);
v_as_x27_4537_ = v_tail_4554_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4556_, lean_object* v_as_x27_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_){
_start:
{
uint8_t v_foundPanic_boxed_4560_; uint8_t v_b_boxed_4561_; lean_object* v_res_4562_; 
v_foundPanic_boxed_4560_ = lean_unbox(v_foundPanic_4556_);
v_b_boxed_4561_ = lean_unbox(v_b_4558_);
v_res_4562_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4560_, v_as_x27_4557_, v_b_boxed_4561_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4563_, uint8_t v_severity_4564_, uint8_t v_isSilent_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = l_Lean_Elab_Command_getRef___redArg(v___y_4566_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4571_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref(v___x_4569_);
v___x_4571_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4570_, v_msgData_4563_, v_severity_4564_, v_isSilent_4565_, v___y_4566_, v___y_4567_);
lean_dec(v_a_4570_);
return v___x_4571_;
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v___y_4566_);
lean_dec_ref(v_msgData_4563_);
v_a_4572_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4569_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4569_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4580_, lean_object* v_severity_4581_, lean_object* v_isSilent_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
uint8_t v_severity_boxed_4586_; uint8_t v_isSilent_boxed_4587_; lean_object* v_res_4588_; 
v_severity_boxed_4586_ = lean_unbox(v_severity_4581_);
v_isSilent_boxed_4587_ = lean_unbox(v_isSilent_4582_);
v_res_4588_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4580_, v_severity_boxed_4586_, v_isSilent_boxed_4587_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v___x_4593_; uint8_t v___x_4594_; lean_object* v___x_4595_; 
v___x_4593_ = 2;
v___x_4594_ = 0;
v___x_4595_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4589_, v___x_4593_, v___x_4594_, v___y_4590_, v___y_4591_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___y_4598_);
return v_res_4600_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4609_ = l_Lean_MessageData_ofFormat(v___x_4608_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v___x_4614_; uint8_t v_foundPanic_4615_; 
v___x_4614_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4610_);
v_foundPanic_4615_ = l_Lean_Syntax_isOfKind(v_x_4610_, v___x_4614_);
if (v_foundPanic_4615_ == 0)
{
lean_object* v___x_4616_; 
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_x_4610_);
v___x_4616_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4616_;
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4617_ = lean_unsigned_to_nat(2u);
v___x_4618_ = l_Lean_Syntax_getArg(v_x_4610_, v___x_4617_);
lean_dec(v_x_4610_);
lean_inc(v_a_4612_);
lean_inc_ref(v_a_4611_);
v___x_4619_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4618_, v_a_4611_, v_a_4612_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; uint8_t v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4676_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref(v___x_4619_);
v___x_4621_ = 0;
v___x_4622_ = l_Lean_MessageLog_toList(v_a_4620_);
v___x_4623_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4615_, v___x_4622_, v___x_4621_);
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4676_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4676_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
uint8_t v___x_4628_; 
v___x_4628_ = lean_unbox(v_a_4624_);
lean_dec(v_a_4624_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; lean_object* v_env_4630_; lean_object* v_scopes_4631_; lean_object* v_usedQuotCtxts_4632_; lean_object* v_nextMacroScope_4633_; lean_object* v_maxRecDepth_4634_; lean_object* v_ngen_4635_; lean_object* v_auxDeclNGen_4636_; lean_object* v_infoState_4637_; lean_object* v_traceState_4638_; lean_object* v_snapshotTasks_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4649_; 
lean_del_object(v___x_4626_);
v___x_4629_ = lean_st_ref_take(v_a_4612_);
v_env_4630_ = lean_ctor_get(v___x_4629_, 0);
v_scopes_4631_ = lean_ctor_get(v___x_4629_, 2);
v_usedQuotCtxts_4632_ = lean_ctor_get(v___x_4629_, 3);
v_nextMacroScope_4633_ = lean_ctor_get(v___x_4629_, 4);
v_maxRecDepth_4634_ = lean_ctor_get(v___x_4629_, 5);
v_ngen_4635_ = lean_ctor_get(v___x_4629_, 6);
v_auxDeclNGen_4636_ = lean_ctor_get(v___x_4629_, 7);
v_infoState_4637_ = lean_ctor_get(v___x_4629_, 8);
v_traceState_4638_ = lean_ctor_get(v___x_4629_, 9);
v_snapshotTasks_4639_ = lean_ctor_get(v___x_4629_, 10);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v___x_4629_, 1);
lean_dec(v_unused_4650_);
v___x_4641_ = v___x_4629_;
v_isShared_4642_ = v_isSharedCheck_4649_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_snapshotTasks_4639_);
lean_inc(v_traceState_4638_);
lean_inc(v_infoState_4637_);
lean_inc(v_auxDeclNGen_4636_);
lean_inc(v_ngen_4635_);
lean_inc(v_maxRecDepth_4634_);
lean_inc(v_nextMacroScope_4633_);
lean_inc(v_usedQuotCtxts_4632_);
lean_inc(v_scopes_4631_);
lean_inc(v_env_4630_);
lean_dec(v___x_4629_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4649_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 1, v_a_4620_);
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_env_4630_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_a_4620_);
lean_ctor_set(v_reuseFailAlloc_4648_, 2, v_scopes_4631_);
lean_ctor_set(v_reuseFailAlloc_4648_, 3, v_usedQuotCtxts_4632_);
lean_ctor_set(v_reuseFailAlloc_4648_, 4, v_nextMacroScope_4633_);
lean_ctor_set(v_reuseFailAlloc_4648_, 5, v_maxRecDepth_4634_);
lean_ctor_set(v_reuseFailAlloc_4648_, 6, v_ngen_4635_);
lean_ctor_set(v_reuseFailAlloc_4648_, 7, v_auxDeclNGen_4636_);
lean_ctor_set(v_reuseFailAlloc_4648_, 8, v_infoState_4637_);
lean_ctor_set(v_reuseFailAlloc_4648_, 9, v_traceState_4638_);
lean_ctor_set(v_reuseFailAlloc_4648_, 10, v_snapshotTasks_4639_);
v___x_4644_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = lean_st_ref_set(v_a_4612_, v___x_4644_);
v___x_4646_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4647_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4646_, v_a_4611_, v_a_4612_);
lean_dec(v_a_4612_);
return v___x_4647_;
}
}
}
else
{
lean_object* v___x_4651_; lean_object* v_env_4652_; lean_object* v_scopes_4653_; lean_object* v_usedQuotCtxts_4654_; lean_object* v_nextMacroScope_4655_; lean_object* v_maxRecDepth_4656_; lean_object* v_ngen_4657_; lean_object* v_auxDeclNGen_4658_; lean_object* v_infoState_4659_; lean_object* v_traceState_4660_; lean_object* v_snapshotTasks_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4674_; 
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4611_);
v___x_4651_ = lean_st_ref_take(v_a_4612_);
v_env_4652_ = lean_ctor_get(v___x_4651_, 0);
v_scopes_4653_ = lean_ctor_get(v___x_4651_, 2);
v_usedQuotCtxts_4654_ = lean_ctor_get(v___x_4651_, 3);
v_nextMacroScope_4655_ = lean_ctor_get(v___x_4651_, 4);
v_maxRecDepth_4656_ = lean_ctor_get(v___x_4651_, 5);
v_ngen_4657_ = lean_ctor_get(v___x_4651_, 6);
v_auxDeclNGen_4658_ = lean_ctor_get(v___x_4651_, 7);
v_infoState_4659_ = lean_ctor_get(v___x_4651_, 8);
v_traceState_4660_ = lean_ctor_get(v___x_4651_, 9);
v_snapshotTasks_4661_ = lean_ctor_get(v___x_4651_, 10);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4674_ == 0)
{
lean_object* v_unused_4675_; 
v_unused_4675_ = lean_ctor_get(v___x_4651_, 1);
lean_dec(v_unused_4675_);
v___x_4663_ = v___x_4651_;
v_isShared_4664_ = v_isSharedCheck_4674_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_snapshotTasks_4661_);
lean_inc(v_traceState_4660_);
lean_inc(v_infoState_4659_);
lean_inc(v_auxDeclNGen_4658_);
lean_inc(v_ngen_4657_);
lean_inc(v_maxRecDepth_4656_);
lean_inc(v_nextMacroScope_4655_);
lean_inc(v_usedQuotCtxts_4654_);
lean_inc(v_scopes_4653_);
lean_inc(v_env_4652_);
lean_dec(v___x_4651_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4674_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4665_; lean_object* v___x_4667_; 
v___x_4665_ = l_Lean_MessageLog_empty;
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 1, v___x_4665_);
v___x_4667_ = v___x_4663_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_env_4652_);
lean_ctor_set(v_reuseFailAlloc_4673_, 1, v___x_4665_);
lean_ctor_set(v_reuseFailAlloc_4673_, 2, v_scopes_4653_);
lean_ctor_set(v_reuseFailAlloc_4673_, 3, v_usedQuotCtxts_4654_);
lean_ctor_set(v_reuseFailAlloc_4673_, 4, v_nextMacroScope_4655_);
lean_ctor_set(v_reuseFailAlloc_4673_, 5, v_maxRecDepth_4656_);
lean_ctor_set(v_reuseFailAlloc_4673_, 6, v_ngen_4657_);
lean_ctor_set(v_reuseFailAlloc_4673_, 7, v_auxDeclNGen_4658_);
lean_ctor_set(v_reuseFailAlloc_4673_, 8, v_infoState_4659_);
lean_ctor_set(v_reuseFailAlloc_4673_, 9, v_traceState_4660_);
lean_ctor_set(v_reuseFailAlloc_4673_, 10, v_snapshotTasks_4661_);
v___x_4667_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4668_ = lean_st_ref_set(v_a_4612_, v___x_4667_);
lean_dec(v_a_4612_);
v___x_4669_ = lean_box(0);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4669_);
v___x_4671_ = v___x_4626_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
v_a_4677_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4619_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4619_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4685_, v_a_4686_, v_a_4687_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4690_, lean_object* v_as_4691_, lean_object* v_as_x27_4692_, uint8_t v_b_4693_, lean_object* v_a_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4690_, v_as_x27_4692_, v_b_4693_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4699_, lean_object* v_as_4700_, lean_object* v_as_x27_4701_, lean_object* v_b_4702_, lean_object* v_a_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
uint8_t v_foundPanic_boxed_4707_; uint8_t v_b_boxed_4708_; lean_object* v_res_4709_; 
v_foundPanic_boxed_4707_ = lean_unbox(v_foundPanic_4699_);
v_b_boxed_4708_ = lean_unbox(v_b_4702_);
v_res_4709_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4707_, v_as_4700_, v_as_x27_4701_, v_b_boxed_4708_, v_a_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v_as_4700_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4718_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4719_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4720_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4721_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4722_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4718_, v___x_4719_, v___x_4720_, v___x_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4724_;
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
