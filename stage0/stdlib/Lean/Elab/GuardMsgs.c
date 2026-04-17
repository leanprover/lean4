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
lean_object* lean_register_option(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Message_isTrace___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "guard_msgs"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 116, 183, 228, 179, 151, 45, 148)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(183, 103, 150, 225, 110, 223, 115, 232)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "When true, show a diff between expected and actual messages if they don't match. "};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabGuardMsgs"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 139, 31, 76, 158, 95, 94, 217)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 103, 231, 132, 249, 141, 167, 146)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(137) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(168) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__0_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(137) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(137) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__3_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object*);
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
static const lean_array_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabGuardPanic"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 139, 31, 76, 158, 95, 94, 217)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 172, 183, 87, 120, 30, 187, 134)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_47_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_48_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v___x_46_, v___x_47_, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(lean_object* v_line_53_, lean_object* v_pos_54_){
_start:
{
lean_object* v_line_55_; lean_object* v_column_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_line_55_ = lean_ctor_get(v_pos_54_, 0);
lean_inc(v_line_55_);
v_column_56_ = lean_ctor_get(v_pos_54_, 1);
lean_inc(v_column_56_);
lean_dec_ref(v_pos_54_);
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0));
v___x_58_ = lean_nat_sub(v_line_55_, v_line_53_);
lean_dec(v_line_55_);
v___x_59_ = l_Nat_reprFast(v___x_58_);
v___x_60_ = lean_string_append(v___x_57_, v___x_59_);
lean_dec_ref(v___x_59_);
v___x_61_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1));
v___x_62_ = lean_string_append(v___x_60_, v___x_61_);
v___x_63_ = l_Nat_reprFast(v_column_56_);
v___x_64_ = lean_string_append(v___x_62_, v___x_63_);
lean_dec_ref(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___boxed(lean_object* v_line_65_, lean_object* v_pos_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_line_65_, v_pos_66_);
lean_dec(v_line_65_);
return v_res_67_;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_78_ = lean_string_utf8_byte_size(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(lean_object* v_msg_81_, lean_object* v_reportPos_x3f_82_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_89_; uint8_t v___y_90_; lean_object* v___y_92_; uint8_t v___y_93_; uint32_t v___y_94_; lean_object* v_str_98_; lean_object* v_pos_110_; lean_object* v_endPos_111_; uint8_t v_severity_112_; lean_object* v_caption_113_; lean_object* v_data_114_; lean_object* v___x_115_; lean_object* v___y_117_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v_str_130_; lean_object* v_str_142_; lean_object* v___y_153_; lean_object* v_str_157_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_pos_110_ = lean_ctor_get(v_msg_81_, 1);
lean_inc_ref(v_pos_110_);
v_endPos_111_ = lean_ctor_get(v_msg_81_, 2);
lean_inc(v_endPos_111_);
v_severity_112_ = lean_ctor_get_uint8(v_msg_81_, sizeof(void*)*5 + 1);
v_caption_113_ = lean_ctor_get(v_msg_81_, 3);
v_data_114_ = lean_ctor_get(v_msg_81_, 4);
lean_inc(v_data_114_);
v___x_115_ = l_Lean_MessageData_toString(v_data_114_);
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_165_ = lean_string_dec_eq(v_caption_113_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11));
lean_inc_ref(v_caption_113_);
v___x_167_ = lean_string_append(v_caption_113_, v___x_166_);
v___x_168_ = lean_string_append(v___x_167_, v___x_115_);
lean_dec_ref(v___x_115_);
v_str_157_ = v___x_168_;
goto v___jp_156_;
}
else
{
v_str_157_ = v___x_115_;
goto v___jp_156_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_87_ = lean_string_append(v___y_85_, v___x_86_);
return v___x_87_;
}
v___jp_88_:
{
if (v___y_90_ == 0)
{
return v___y_89_;
}
else
{
v___y_85_ = v___y_89_;
goto v___jp_84_;
}
}
v___jp_91_:
{
uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 10;
v___x_96_ = lean_uint32_dec_eq(v___y_94_, v___x_95_);
if (v___x_96_ == 0)
{
v___y_85_ = v___y_92_;
goto v___jp_84_;
}
else
{
v___y_89_ = v___y_92_;
v___y_90_ = v___y_93_;
goto v___jp_88_;
}
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_string_utf8_byte_size(v_str_98_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_inc_ref(v_str_98_);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v_str_98_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
v___x_103_ = l_String_Slice_Pos_prev_x3f(v___x_102_, v___x_99_);
if (lean_obj_tag(v___x_103_) == 0)
{
uint32_t v___x_104_; 
lean_dec_ref(v___x_102_);
v___x_104_ = 65;
v___y_92_ = v_str_98_;
v___y_93_ = v___x_101_;
v___y_94_ = v___x_104_;
goto v___jp_91_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; 
v_val_105_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_105_);
lean_dec_ref(v___x_103_);
v___x_106_ = l_String_Slice_Pos_get_x3f(v___x_102_, v_val_105_);
lean_dec(v_val_105_);
lean_dec_ref(v___x_102_);
if (lean_obj_tag(v___x_106_) == 0)
{
uint32_t v___x_107_; 
v___x_107_ = 65;
v___y_92_ = v_str_98_;
v___y_93_ = v___x_101_;
v___y_94_ = v___x_107_;
goto v___jp_91_;
}
else
{
lean_object* v_val_108_; uint32_t v___x_109_; 
v_val_108_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_val_108_);
lean_dec_ref(v___x_106_);
v___x_109_ = lean_unbox_uint32(v_val_108_);
lean_dec(v_val_108_);
v___y_92_ = v_str_98_;
v___y_93_ = v___x_101_;
v___y_94_ = v___x_109_;
goto v___jp_91_;
}
}
}
else
{
v___y_89_ = v_str_98_;
v___y_90_ = v___x_101_;
goto v___jp_88_;
}
}
v___jp_116_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_121_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_118_, v_pos_110_);
v___x_122_ = lean_string_append(v___x_120_, v___x_121_);
lean_dec_ref(v___x_121_);
v___x_123_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = lean_string_append(v___x_124_, v___y_119_);
lean_dec_ref(v___y_119_);
v___x_126_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = lean_string_append(v___x_127_, v___y_117_);
lean_dec_ref(v___y_117_);
v_str_98_ = v___x_128_;
goto v___jp_97_;
}
v___jp_129_:
{
if (lean_obj_tag(v_reportPos_x3f_82_) == 1)
{
if (lean_obj_tag(v_endPos_111_) == 0)
{
lean_object* v_val_131_; lean_object* v___x_132_; 
v_val_131_ = lean_ctor_get(v_reportPos_x3f_82_, 0);
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_117_ = v_str_130_;
v___y_118_ = v_val_131_;
v___y_119_ = v___x_132_;
goto v___jp_116_;
}
else
{
lean_object* v_val_133_; lean_object* v_val_134_; lean_object* v_line_135_; lean_object* v_column_136_; lean_object* v_line_137_; uint8_t v___x_138_; 
v_val_133_ = lean_ctor_get(v_endPos_111_, 0);
lean_inc(v_val_133_);
lean_dec_ref(v_endPos_111_);
v_val_134_ = lean_ctor_get(v_reportPos_x3f_82_, 0);
v_line_135_ = lean_ctor_get(v_val_133_, 0);
v_column_136_ = lean_ctor_get(v_val_133_, 1);
v_line_137_ = lean_ctor_get(v_pos_110_, 0);
v___x_138_ = lean_nat_dec_eq(v_line_135_, v_line_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_134_, v_val_133_);
v___y_117_ = v_str_130_;
v___y_118_ = v_val_134_;
v___y_119_ = v___x_139_;
goto v___jp_116_;
}
else
{
lean_object* v___x_140_; 
lean_inc(v_column_136_);
lean_dec(v_val_133_);
v___x_140_ = l_Nat_reprFast(v_column_136_);
v___y_117_ = v_str_130_;
v___y_118_ = v_val_134_;
v___y_119_ = v___x_140_;
goto v___jp_116_;
}
}
}
else
{
lean_dec(v_endPos_111_);
lean_dec_ref(v_pos_110_);
v_str_98_ = v_str_130_;
goto v___jp_97_;
}
}
v___jp_141_:
{
uint8_t v___x_143_; 
v___x_143_ = l_Lean_Message_isTrace(v_msg_81_);
lean_dec_ref(v_msg_81_);
if (v___x_143_ == 0)
{
switch(v_severity_112_)
{
case 0:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4));
v___x_145_ = lean_string_append(v___x_144_, v_str_142_);
lean_dec_ref(v_str_142_);
v_str_130_ = v___x_145_;
goto v___jp_129_;
}
case 1:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5));
v___x_147_ = lean_string_append(v___x_146_, v_str_142_);
lean_dec_ref(v_str_142_);
v_str_130_ = v___x_147_;
goto v___jp_129_;
}
default: 
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6));
v___x_149_ = lean_string_append(v___x_148_, v_str_142_);
lean_dec_ref(v_str_142_);
v_str_130_ = v___x_149_;
goto v___jp_129_;
}
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7));
v___x_151_ = lean_string_append(v___x_150_, v_str_142_);
lean_dec_ref(v_str_142_);
v_str_130_ = v___x_151_;
goto v___jp_129_;
}
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_155_ = lean_string_append(v___x_154_, v___y_153_);
lean_dec_ref(v___y_153_);
v_str_142_ = v___x_155_;
goto v___jp_141_;
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_159_ = lean_string_utf8_byte_size(v_str_157_);
v___x_160_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_161_ = lean_nat_dec_le(v___x_160_, v___x_159_);
if (v___x_161_ == 0)
{
v___y_153_ = v_str_157_;
goto v___jp_152_;
}
else
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_string_memcmp(v_str_157_, v___x_158_, v___x_162_, v___x_162_, v___x_160_);
if (v___x_163_ == 0)
{
v___y_153_ = v_str_157_;
goto v___jp_152_;
}
else
{
v_str_142_ = v_str_157_;
goto v___jp_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object* v_msg_169_, lean_object* v_reportPos_x3f_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_169_, v_reportPos_x3f_170_);
lean_dec(v_reportPos_x3f_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(uint8_t v_x_173_){
_start:
{
switch(v_x_173_)
{
case 0:
{
lean_object* v___x_174_; 
v___x_174_ = lean_unsigned_to_nat(0u);
return v___x_174_;
}
case 1:
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(1u);
return v___x_175_;
}
default: 
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(2u);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___boxed(lean_object* v_x_177_){
_start:
{
uint8_t v_x_boxed_178_; lean_object* v_res_179_; 
v_x_boxed_178_ = lean_unbox(v_x_177_);
v_res_179_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_boxed_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(uint8_t v_x_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx___boxed(lean_object* v_x_182_){
_start:
{
uint8_t v_x_4__boxed_183_; lean_object* v_res_184_; 
v_x_4__boxed_183_ = lean_unbox(v_x_182_);
v_res_184_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(v_x_4__boxed_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_185_){
_start:
{
lean_inc(v_k_185_);
return v_k_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_186_);
lean_dec(v_k_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_188_, lean_object* v_ctorIdx_189_, uint8_t v_t_190_, lean_object* v_h_191_, lean_object* v_k_192_){
_start:
{
lean_inc(v_k_192_);
return v_k_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
uint8_t v_t_boxed_198_; lean_object* v_res_199_; 
v_t_boxed_198_ = lean_unbox(v_t_195_);
v_res_199_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_193_, v_ctorIdx_194_, v_t_boxed_198_, v_h_196_, v_k_197_);
lean_dec(v_k_197_);
lean_dec(v_ctorIdx_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_200_){
_start:
{
lean_inc(v_check_200_);
return v_check_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_201_);
lean_dec(v_check_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_203_, uint8_t v_t_204_, lean_object* v_h_205_, lean_object* v_check_206_){
_start:
{
lean_inc(v_check_206_);
return v_check_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_207_, lean_object* v_t_208_, lean_object* v_h_209_, lean_object* v_check_210_){
_start:
{
uint8_t v_t_boxed_211_; lean_object* v_res_212_; 
v_t_boxed_211_ = lean_unbox(v_t_208_);
v_res_212_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_207_, v_t_boxed_211_, v_h_209_, v_check_210_);
lean_dec(v_check_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_213_){
_start:
{
lean_inc(v_drop_213_);
return v_drop_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_214_);
lean_dec(v_drop_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_216_, uint8_t v_t_217_, lean_object* v_h_218_, lean_object* v_drop_219_){
_start:
{
lean_inc(v_drop_219_);
return v_drop_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_drop_223_){
_start:
{
uint8_t v_t_boxed_224_; lean_object* v_res_225_; 
v_t_boxed_224_ = lean_unbox(v_t_221_);
v_res_225_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_220_, v_t_boxed_224_, v_h_222_, v_drop_223_);
lean_dec(v_drop_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_226_){
_start:
{
lean_inc(v_pass_226_);
return v_pass_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_227_);
lean_dec(v_pass_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_229_, uint8_t v_t_230_, lean_object* v_h_231_, lean_object* v_pass_232_){
_start:
{
lean_inc(v_pass_232_);
return v_pass_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_pass_236_){
_start:
{
uint8_t v_t_boxed_237_; lean_object* v_res_238_; 
v_t_boxed_237_ = lean_unbox(v_t_234_);
v_res_238_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_233_, v_t_boxed_237_, v_h_235_, v_pass_236_);
lean_dec(v_pass_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t v_x_239_){
_start:
{
switch(v_x_239_)
{
case 0:
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
return v___x_240_;
}
case 1:
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(1u);
return v___x_241_;
}
default: 
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(2u);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_x_boxed_244_; lean_object* v_res_245_; 
v_x_boxed_244_ = lean_unbox(v_x_243_);
v_res_245_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_boxed_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(uint8_t v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx___boxed(lean_object* v_x_248_){
_start:
{
uint8_t v_x_4__boxed_249_; lean_object* v_res_250_; 
v_x_4__boxed_249_ = lean_unbox(v_x_248_);
v_res_250_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(v_x_4__boxed_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_251_){
_start:
{
lean_inc(v_k_251_);
return v_k_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_252_);
lean_dec(v_k_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_254_, lean_object* v_ctorIdx_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_k_258_){
_start:
{
lean_inc(v_k_258_);
return v_k_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_259_, lean_object* v_ctorIdx_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_k_263_){
_start:
{
uint8_t v_t_boxed_264_; lean_object* v_res_265_; 
v_t_boxed_264_ = lean_unbox(v_t_261_);
v_res_265_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_259_, v_ctorIdx_260_, v_t_boxed_264_, v_h_262_, v_k_263_);
lean_dec(v_k_263_);
lean_dec(v_ctorIdx_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_266_){
_start:
{
lean_inc(v_exact_266_);
return v_exact_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_267_);
lean_dec(v_exact_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_269_, uint8_t v_t_270_, lean_object* v_h_271_, lean_object* v_exact_272_){
_start:
{
lean_inc(v_exact_272_);
return v_exact_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_exact_276_){
_start:
{
uint8_t v_t_boxed_277_; lean_object* v_res_278_; 
v_t_boxed_277_ = lean_unbox(v_t_274_);
v_res_278_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_273_, v_t_boxed_277_, v_h_275_, v_exact_276_);
lean_dec(v_exact_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_279_){
_start:
{
lean_inc(v_normalized_279_);
return v_normalized_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_280_);
lean_dec(v_normalized_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_282_, uint8_t v_t_283_, lean_object* v_h_284_, lean_object* v_normalized_285_){
_start:
{
lean_inc(v_normalized_285_);
return v_normalized_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_286_, lean_object* v_t_287_, lean_object* v_h_288_, lean_object* v_normalized_289_){
_start:
{
uint8_t v_t_boxed_290_; lean_object* v_res_291_; 
v_t_boxed_290_ = lean_unbox(v_t_287_);
v_res_291_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_286_, v_t_boxed_290_, v_h_288_, v_normalized_289_);
lean_dec(v_normalized_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_292_){
_start:
{
lean_inc(v_lax_292_);
return v_lax_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_293_);
lean_dec(v_lax_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_295_, uint8_t v_t_296_, lean_object* v_h_297_, lean_object* v_lax_298_){
_start:
{
lean_inc(v_lax_298_);
return v_lax_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_299_, lean_object* v_t_300_, lean_object* v_h_301_, lean_object* v_lax_302_){
_start:
{
uint8_t v_t_boxed_303_; lean_object* v_res_304_; 
v_t_boxed_303_ = lean_unbox(v_t_300_);
v_res_304_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_299_, v_t_boxed_303_, v_h_301_, v_lax_302_);
lean_dec(v_lax_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t v_x_305_){
_start:
{
if (v_x_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_unsigned_to_nat(0u);
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(1u);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object* v_x_308_){
_start:
{
uint8_t v_x_boxed_309_; lean_object* v_res_310_; 
v_x_boxed_309_ = lean_unbox(v_x_308_);
v_res_310_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_boxed_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(uint8_t v_x_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx___boxed(lean_object* v_x_313_){
_start:
{
uint8_t v_x_4__boxed_314_; lean_object* v_res_315_; 
v_x_4__boxed_314_ = lean_unbox(v_x_313_);
v_res_315_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(v_x_4__boxed_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_316_){
_start:
{
lean_inc(v_k_316_);
return v_k_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_317_);
lean_dec(v_k_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_319_, lean_object* v_ctorIdx_320_, uint8_t v_t_321_, lean_object* v_h_322_, lean_object* v_k_323_){
_start:
{
lean_inc(v_k_323_);
return v_k_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_324_, lean_object* v_ctorIdx_325_, lean_object* v_t_326_, lean_object* v_h_327_, lean_object* v_k_328_){
_start:
{
uint8_t v_t_boxed_329_; lean_object* v_res_330_; 
v_t_boxed_329_ = lean_unbox(v_t_326_);
v_res_330_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_324_, v_ctorIdx_325_, v_t_boxed_329_, v_h_327_, v_k_328_);
lean_dec(v_k_328_);
lean_dec(v_ctorIdx_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_331_){
_start:
{
lean_inc(v_exact_331_);
return v_exact_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_332_);
lean_dec(v_exact_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_334_, uint8_t v_t_335_, lean_object* v_h_336_, lean_object* v_exact_337_){
_start:
{
lean_inc(v_exact_337_);
return v_exact_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_exact_341_){
_start:
{
uint8_t v_t_boxed_342_; lean_object* v_res_343_; 
v_t_boxed_342_ = lean_unbox(v_t_339_);
v_res_343_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_338_, v_t_boxed_342_, v_h_340_, v_exact_341_);
lean_dec(v_exact_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_344_){
_start:
{
lean_inc(v_sorted_344_);
return v_sorted_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_345_);
lean_dec(v_sorted_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_347_, uint8_t v_t_348_, lean_object* v_h_349_, lean_object* v_sorted_350_){
_start:
{
lean_inc(v_sorted_350_);
return v_sorted_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_sorted_354_){
_start:
{
uint8_t v_t_boxed_355_; lean_object* v_res_356_; 
v_t_boxed_355_ = lean_unbox(v_t_352_);
v_res_356_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_351_, v_t_boxed_355_, v_h_353_, v_sorted_354_);
lean_dec(v_sorted_354_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_box(0);
v___x_358_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
if (lean_obj_tag(v_action_x3f_393_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_428_; 
v_val_397_ = lean_ctor_get(v_action_x3f_393_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_action_x3f_393_);
if (v_isSharedCheck_428_ == 0)
{
v___x_399_ = v_action_x3f_393_;
v_isShared_400_ = v_isSharedCheck_428_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_val_397_);
lean_dec(v_action_x3f_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_428_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2));
lean_inc(v_val_397_);
v___x_402_ = l_Lean_Syntax_isOfKind(v_val_397_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
lean_del_object(v___x_399_);
lean_dec(v_val_397_);
v___x_403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_Syntax_getArg(v_val_397_, v___x_404_);
lean_dec(v_val_397_);
v___x_406_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5));
lean_inc(v___x_405_);
v___x_407_ = l_Lean_Syntax_isOfKind(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7));
lean_inc(v___x_405_);
v___x_409_ = l_Lean_Syntax_isOfKind(v___x_405_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__9));
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_405_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_del_object(v___x_399_);
v___x_412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_412_;
}
else
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_413_ = 2;
v___x_414_ = lean_box(v___x_413_);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v___x_414_);
v___x_416_ = v___x_399_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
lean_dec(v___x_405_);
v___x_418_ = 1;
v___x_419_ = lean_box(v___x_418_);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v___x_419_);
v___x_421_ = v___x_399_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec(v___x_405_);
v___x_423_ = 0;
v___x_424_ = lean_box(v___x_423_);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v___x_424_);
v___x_426_ = v___x_399_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
else
{
uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_action_x3f_393_);
v___x_429_ = 0;
v___x_430_ = lean_box(v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_437_, lean_object* v_x_438_){
_start:
{
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_439_, lean_object* v_x_440_){
_start:
{
uint8_t v___x_1582__boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v___x_1582__boxed_441_ = lean_unbox(v___x_439_);
v_res_442_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_1582__boxed_441_, v_x_440_);
lean_dec_ref(v_x_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_444_, lean_object* v_msg_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_Message_isTrace(v_msg_445_);
if (v___x_446_ == 0)
{
uint8_t v_severity_447_; uint8_t v___x_448_; uint8_t v___x_449_; 
v_severity_447_ = lean_ctor_get_uint8(v_msg_445_, sizeof(void*)*5 + 1);
v___x_448_ = 2;
v___x_449_ = l_Lean_instBEqMessageSeverity_beq(v_severity_447_, v___x_448_);
return v___x_449_;
}
else
{
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_450_, lean_object* v_msg_451_){
_start:
{
uint8_t v___x_1588__boxed_452_; uint8_t v_res_453_; lean_object* v_r_454_; 
v___x_1588__boxed_452_ = lean_unbox(v___x_450_);
v_res_453_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_1588__boxed_452_, v_msg_451_);
lean_dec_ref(v_msg_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_455_, lean_object* v_msg_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Message_isTrace(v_msg_456_);
if (v___x_457_ == 0)
{
uint8_t v_severity_458_; uint8_t v___x_459_; uint8_t v___x_460_; 
v_severity_458_ = lean_ctor_get_uint8(v_msg_456_, sizeof(void*)*5 + 1);
v___x_459_ = 1;
v___x_460_ = l_Lean_instBEqMessageSeverity_beq(v_severity_458_, v___x_459_);
return v___x_460_;
}
else
{
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_461_, lean_object* v_msg_462_){
_start:
{
uint8_t v___x_1597__boxed_463_; uint8_t v_res_464_; lean_object* v_r_465_; 
v___x_1597__boxed_463_ = lean_unbox(v___x_461_);
v_res_464_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_1597__boxed_463_, v_msg_462_);
lean_dec_ref(v_msg_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_466_, lean_object* v_msg_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = l_Lean_Message_isTrace(v_msg_467_);
if (v___x_468_ == 0)
{
uint8_t v_severity_469_; uint8_t v___x_470_; uint8_t v___x_471_; 
v_severity_469_ = lean_ctor_get_uint8(v_msg_467_, sizeof(void*)*5 + 1);
v___x_470_ = 0;
v___x_471_ = l_Lean_instBEqMessageSeverity_beq(v_severity_469_, v___x_470_);
return v___x_471_;
}
else
{
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_472_, lean_object* v_msg_473_){
_start:
{
uint8_t v___x_1606__boxed_474_; uint8_t v_res_475_; lean_object* v_r_476_; 
v___x_1606__boxed_474_ = lean_unbox(v___x_472_);
v_res_475_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_1606__boxed_474_, v_msg_473_);
lean_dec_ref(v_msg_473_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_502_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_502_);
v___x_505_ = l_Lean_Syntax_isOfKind(v_x_502_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec(v_x_502_);
v___x_506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = l_Lean_Syntax_getArg(v_x_502_, v___x_507_);
lean_dec(v_x_502_);
v___x_509_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_508_);
v___x_510_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_508_);
v___x_512_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_508_);
v___x_514_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_508_);
v___x_516_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_518_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v___x_520_ = lean_box(v___x_518_);
v___f_521_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_521_, 0, v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___f_521_);
return v___x_522_;
}
}
else
{
lean_object* v___x_523_; lean_object* v___f_524_; lean_object* v___x_525_; 
lean_dec(v___x_508_);
v___x_523_ = lean_box(v___x_514_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_524_, 0, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___f_524_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; 
lean_dec(v___x_508_);
v___x_526_ = lean_box(v___x_512_);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_527_, 0, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___f_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
lean_dec(v___x_508_);
v___x_529_ = lean_box(v___x_510_);
v___f_530_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_530_, 0, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___f_530_);
return v___x_531_;
}
}
else
{
lean_object* v___f_532_; lean_object* v___x_533_; 
lean_dec(v___x_508_);
v___f_532_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___f_532_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_537_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_546_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_547_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = 0;
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_549_);
lean_dec_ref(v_x_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_552_, lean_object* v___y_553_){
_start:
{
if (lean_obj_tag(v_snd_552_) == 0)
{
uint8_t v___x_554_; 
lean_dec_ref(v___y_553_);
v___x_554_ = 0;
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_val_555_ = lean_ctor_get(v_snd_552_, 0);
lean_inc(v_val_555_);
lean_dec_ref(v_snd_552_);
v___x_556_ = lean_apply_1(v_val_555_, v___y_553_);
v___x_557_ = lean_unbox(v___x_556_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_558_, lean_object* v___y_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_558_, v___y_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_562_, lean_object* v_snd_563_, uint8_t v_a_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
lean_inc_ref(v___y_565_);
v___x_566_ = lean_apply_1(v_a_562_, v___y_565_);
v___x_567_ = lean_unbox(v___x_566_);
if (v___x_567_ == 0)
{
if (lean_obj_tag(v_snd_563_) == 0)
{
uint8_t v___x_568_; 
lean_dec_ref(v___y_565_);
v___x_568_ = 2;
return v___x_568_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_val_569_ = lean_ctor_get(v_snd_563_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v_snd_563_);
v___x_570_ = lean_apply_1(v_val_569_, v___y_565_);
v___x_571_ = lean_unbox(v___x_570_);
return v___x_571_;
}
}
else
{
lean_dec_ref(v___y_565_);
lean_dec(v_snd_563_);
return v_a_564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_572_, lean_object* v_snd_573_, lean_object* v_a_574_, lean_object* v___y_575_){
_start:
{
uint8_t v_a_11570__boxed_576_; uint8_t v_res_577_; lean_object* v_r_578_; 
v_a_11570__boxed_576_ = lean_unbox(v_a_574_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_572_, v_snd_573_, v_a_11570__boxed_576_, v___y_575_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_639_, size_t v_sz_640_, size_t v_i_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_a_647_; uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_641_, v_sz_640_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_b_642_);
return v___x_652_;
}
else
{
lean_object* v_snd_653_; lean_object* v_snd_654_; lean_object* v_snd_655_; lean_object* v_fst_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_963_; 
v_snd_653_ = lean_ctor_get(v_b_642_, 1);
lean_inc(v_snd_653_);
v_snd_654_ = lean_ctor_get(v_snd_653_, 1);
lean_inc(v_snd_654_);
v_snd_655_ = lean_ctor_get(v_snd_654_, 1);
lean_inc(v_snd_655_);
v_fst_656_ = lean_ctor_get(v_b_642_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_b_642_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_b_642_, 1);
lean_dec(v_unused_964_);
v___x_658_ = v_b_642_;
v_isShared_659_ = v_isSharedCheck_963_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_fst_656_);
lean_dec(v_b_642_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_963_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_fst_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_961_; 
v_fst_660_ = lean_ctor_get(v_snd_653_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_snd_653_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_snd_653_, 1);
lean_dec(v_unused_962_);
v___x_662_ = v_snd_653_;
v_isShared_663_ = v_isSharedCheck_961_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_fst_660_);
lean_dec(v_snd_653_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_961_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_fst_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_959_; 
v_fst_664_ = lean_ctor_get(v_snd_654_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_snd_654_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_snd_654_, 1);
lean_dec(v_unused_960_);
v___x_666_ = v_snd_654_;
v_isShared_667_ = v_isSharedCheck_959_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_fst_664_);
lean_dec(v_snd_654_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_959_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_958_; 
v_fst_668_ = lean_ctor_get(v_snd_655_, 0);
v_snd_669_ = lean_ctor_get(v_snd_655_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_snd_655_);
if (v_isSharedCheck_958_ == 0)
{
v___x_671_ = v_snd_655_;
v_isShared_672_ = v_isSharedCheck_958_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v_snd_655_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_958_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_a_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_a_673_ = lean_array_uget_borrowed(v_as_639_, v_i_641_);
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_673_);
v___x_675_ = l_Lean_Syntax_isOfKind(v_a_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_678_; 
lean_dec_ref(v___x_676_);
if (v_isShared_672_ == 0)
{
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_snd_669_);
v___x_678_ = v_reuseFailAlloc_688_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_678_);
v___x_680_ = v___x_666_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_fst_664_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_687_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_680_);
v___x_682_ = v___x_662_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_660_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_682_);
v___x_684_ = v___x_658_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_656_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v_a_647_ = v___x_684_;
goto v___jp_646_;
}
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_del_object(v___x_671_);
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
lean_dec(v_fst_656_);
v_a_689_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_676_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_676_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_action_x3f_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_Lean_Syntax_getArg(v_a_673_, v___x_697_);
v___x_739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_698_);
v___x_740_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; uint8_t v___x_742_; 
lean_del_object(v___x_671_);
lean_del_object(v___x_666_);
lean_del_object(v___x_662_);
lean_del_object(v___x_658_);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_698_);
v___x_742_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; uint8_t v_reportPositions_744_; 
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_698_);
v_reportPositions_744_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_743_);
if (v_reportPositions_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_698_);
v___x_746_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_698_);
v___x_748_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v___x_698_);
v___x_749_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v___x_749_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_fst_668_);
lean_ctor_set(v___x_750_, 1, v_snd_669_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_fst_664_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_fst_660_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_fst_656_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v_a_647_ = v___x_753_;
goto v___jp_646_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_754_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_749_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_749_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(2u);
v___x_763_ = l_Lean_Syntax_getArg(v___x_698_, v___x_762_);
lean_dec(v___x_698_);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_763_);
v___x_765_ = l_Lean_Syntax_isOfKind(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_767_ = l_Lean_Syntax_isOfKind(v___x_763_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v___x_768_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_fst_668_);
lean_ctor_set(v___x_769_, 1, v_snd_669_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_fst_664_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_fst_660_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_fst_656_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v_a_647_ = v___x_772_;
goto v___jp_646_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_773_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_768_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_768_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec(v_fst_668_);
v___x_781_ = lean_box(v_reportPositions_744_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_snd_669_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_fst_664_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_fst_660_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_fst_656_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v_a_647_ = v___x_785_;
goto v___jp_646_;
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v___x_763_);
lean_dec(v_fst_668_);
v___x_786_ = lean_box(v___x_675_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v_snd_669_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_fst_664_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_660_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_fst_656_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v_a_647_ = v___x_790_;
goto v___jp_646_;
}
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_791_ = lean_unsigned_to_nat(2u);
v___x_792_ = l_Lean_Syntax_getArg(v___x_698_, v___x_791_);
lean_dec(v___x_698_);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_792_);
v___x_794_ = l_Lean_Syntax_isOfKind(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v___x_792_);
v___x_795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v___x_795_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_fst_668_);
lean_ctor_set(v___x_796_, 1, v_snd_669_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_664_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_fst_660_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_656_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v_a_647_ = v___x_799_;
goto v___jp_646_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_800_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_795_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_808_ = l_Lean_Syntax_getArg(v___x_792_, v___x_697_);
lean_dec(v___x_792_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_808_);
v___x_810_ = l_Lean_Syntax_isOfKind(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_812_ = l_Lean_Syntax_isOfKind(v___x_808_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v___x_813_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_fst_668_);
lean_ctor_set(v___x_814_, 1, v_snd_669_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_fst_664_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_fst_660_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_fst_656_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v_a_647_ = v___x_817_;
goto v___jp_646_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_818_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_813_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_813_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v_fst_664_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_fst_668_);
lean_ctor_set(v___x_826_, 1, v_snd_669_);
v___x_827_ = lean_box(v_reportPositions_744_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_fst_660_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_fst_656_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v_a_647_ = v___x_830_;
goto v___jp_646_;
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v___x_808_);
lean_dec(v_fst_664_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_fst_668_);
lean_ctor_set(v___x_831_, 1, v_snd_669_);
v___x_832_ = lean_box(v___x_675_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_fst_660_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_fst_656_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v_a_647_ = v___x_835_;
goto v___jp_646_;
}
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_836_ = lean_unsigned_to_nat(2u);
v___x_837_ = l_Lean_Syntax_getArg(v___x_698_, v___x_836_);
lean_dec(v___x_698_);
v___x_838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_837_);
v___x_839_ = l_Lean_Syntax_isOfKind(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_dec(v___x_837_);
v___x_840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec_ref(v___x_840_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_fst_668_);
lean_ctor_set(v___x_841_, 1, v_snd_669_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_fst_664_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_fst_660_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_fst_656_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v_a_647_ = v___x_844_;
goto v___jp_646_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_845_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_840_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_840_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = l_Lean_Syntax_getArg(v___x_837_, v___x_697_);
lean_dec(v___x_837_);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_853_);
v___x_855_ = l_Lean_Syntax_isOfKind(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_857_ = l_Lean_Syntax_isOfKind(v___x_853_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v___x_858_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_fst_668_);
lean_ctor_set(v___x_859_, 1, v_snd_669_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_fst_664_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_fst_660_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_fst_656_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v_a_647_ = v___x_862_;
goto v___jp_646_;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_863_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_858_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_858_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v_fst_660_);
v___x_871_ = 1;
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_fst_668_);
lean_ctor_set(v___x_872_, 1, v_snd_669_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_fst_664_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_box(v___x_871_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_fst_656_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v_a_647_ = v___x_876_;
goto v___jp_646_;
}
}
else
{
uint8_t v_ordering_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v___x_853_);
lean_dec(v_fst_660_);
v_ordering_877_ = 0;
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_fst_668_);
lean_ctor_set(v___x_878_, 1, v_snd_669_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_fst_664_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_box(v_ordering_877_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___x_879_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_fst_656_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v_a_647_ = v___x_882_;
goto v___jp_646_;
}
}
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_883_ = lean_unsigned_to_nat(2u);
v___x_884_ = l_Lean_Syntax_getArg(v___x_698_, v___x_883_);
lean_dec(v___x_698_);
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_884_);
v___x_886_ = l_Lean_Syntax_isOfKind(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v___x_884_);
v___x_887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec_ref(v___x_887_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_fst_668_);
lean_ctor_set(v___x_888_, 1, v_snd_669_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_fst_664_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_fst_660_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_fst_656_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v_a_647_ = v___x_891_;
goto v___jp_646_;
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_892_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_887_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_887_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = l_Lean_Syntax_getArg(v___x_884_, v___x_697_);
lean_dec(v___x_884_);
v___x_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_900_);
v___x_902_ = l_Lean_Syntax_isOfKind(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_900_);
v___x_904_ = l_Lean_Syntax_isOfKind(v___x_900_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_906_ = l_Lean_Syntax_isOfKind(v___x_900_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref(v___x_907_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_fst_668_);
lean_ctor_set(v___x_908_, 1, v_snd_669_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_fst_664_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_fst_660_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_fst_656_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v_a_647_ = v___x_911_;
goto v___jp_646_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_912_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_907_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_907_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_fst_656_);
v___x_920_ = 2;
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_fst_668_);
lean_ctor_set(v___x_921_, 1, v_snd_669_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_fst_664_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_fst_660_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_box(v___x_920_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
v_a_647_ = v___x_925_;
goto v___jp_646_;
}
}
else
{
uint8_t v_whitespace_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v___x_900_);
lean_dec(v_fst_656_);
v_whitespace_926_ = 1;
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_668_);
lean_ctor_set(v___x_927_, 1, v_snd_669_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_fst_664_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_fst_660_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_box(v_whitespace_926_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_929_);
v_a_647_ = v___x_931_;
goto v___jp_646_;
}
}
else
{
uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v___x_900_);
lean_dec(v_fst_656_);
v___x_932_ = 0;
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_fst_668_);
lean_ctor_set(v___x_933_, 1, v_snd_669_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_664_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_fst_660_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_box(v___x_932_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
v_a_647_ = v___x_937_;
goto v___jp_646_;
}
}
}
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = l_Lean_Syntax_getArg(v___x_698_, v___x_697_);
v___x_939_ = l_Lean_Syntax_isNone(v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_938_);
v___x_941_ = l_Lean_Syntax_matchesNull(v___x_938_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v___x_938_);
lean_dec(v___x_698_);
lean_del_object(v___x_671_);
lean_del_object(v___x_666_);
lean_del_object(v___x_662_);
lean_del_object(v___x_658_);
v___x_942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec_ref(v___x_942_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_fst_668_);
lean_ctor_set(v___x_943_, 1, v_snd_669_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_fst_664_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_fst_660_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_fst_656_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v_a_647_ = v___x_946_;
goto v___jp_646_;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_dec(v_fst_664_);
lean_dec(v_fst_660_);
lean_dec(v_fst_656_);
v_a_947_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_942_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_942_);
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
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Lean_Syntax_getArg(v___x_938_, v___x_697_);
lean_dec(v___x_938_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
v_action_x3f_700_ = v___x_956_;
v___y_701_ = v___y_643_;
v___y_702_ = v___y_644_;
goto v___jp_699_;
}
}
else
{
lean_object* v___x_957_; 
lean_dec(v___x_938_);
v___x_957_ = lean_box(0);
v_action_x3f_700_ = v___x_957_;
v___y_701_ = v___y_643_;
v___y_702_ = v___y_644_;
goto v___jp_699_;
}
}
v___jp_699_:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = l_Lean_Syntax_getArg(v___x_698_, v___x_705_);
lean_dec(v___x_698_);
v___x_707_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___f_709_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_709_, 0, v_a_708_);
lean_closure_set(v___f_709_, 1, v_snd_669_);
lean_closure_set(v___f_709_, 2, v_a_704_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___f_709_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_710_);
v___x_712_ = v___x_671_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_722_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_712_);
v___x_714_ = v___x_666_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_664_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_721_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_714_);
v___x_716_ = v___x_662_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_660_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_716_);
v___x_718_ = v___x_658_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_656_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v_a_647_ = v___x_718_;
goto v___jp_646_;
}
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_704_);
lean_del_object(v___x_671_);
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
lean_dec(v_fst_656_);
v_a_723_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_707_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_707_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v___x_698_);
lean_del_object(v___x_671_);
lean_dec(v_snd_669_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
lean_dec(v_fst_656_);
v_a_731_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_703_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_703_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
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
v___jp_646_:
{
size_t v___x_648_; size_t v___x_649_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_641_, v___x_648_);
v_i_641_ = v___x_649_;
v_b_642_ = v_a_647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_965_, lean_object* v_sz_966_, lean_object* v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
size_t v_sz_boxed_972_; size_t v_i_boxed_973_; lean_object* v_res_974_; 
v_sz_boxed_972_ = lean_unbox_usize(v_sz_966_);
lean_dec(v_sz_966_);
v_i_boxed_973_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_965_, v_sz_boxed_972_, v_i_boxed_973_, v_b_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_as_965_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_975_, size_t v_i_976_, lean_object* v_bs_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v_bs_977_);
return v___x_979_;
}
else
{
lean_object* v_v_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_v_980_ = lean_array_uget(v_bs_977_, v_i_976_);
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_980_);
v___x_982_ = l_Lean_Syntax_isOfKind(v_v_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_dec(v_v_980_);
lean_dec_ref(v_bs_977_);
v___x_983_ = lean_box(0);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v_bs_x27_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v_bs_x27_985_ = lean_array_uset(v_bs_977_, v_i_976_, v___x_984_);
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_976_, v___x_986_);
v___x_988_ = lean_array_uset(v_bs_x27_985_, v_i_976_, v_v_980_);
v_i_976_ = v___x_987_;
v_bs_977_ = v___x_988_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_bs_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_993_, v_i_boxed_994_, v_bs_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_996_, lean_object* v_as_997_, size_t v_i_998_, size_t v_stop_999_, lean_object* v_b_1000_){
_start:
{
lean_object* v___y_1002_; uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_998_, v_stop_999_);
if (v___x_1006_ == 0)
{
lean_object* v_fst_1007_; uint8_t v___x_1008_; 
v_fst_1007_ = lean_ctor_get(v_b_1000_, 0);
v___x_1008_ = lean_unbox(v_fst_1007_);
if (v___x_1008_ == 0)
{
lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_snd_1009_ = lean_ctor_get(v_b_1000_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_b_1000_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_b_1000_, 0);
lean_dec(v_unused_1018_);
v___x_1011_ = v_b_1000_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_dec(v_b_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_box(v___x_996_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_snd_1009_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v___y_1002_ = v___x_1015_;
goto v___jp_1001_;
}
}
}
else
{
lean_object* v_snd_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_snd_1019_ = lean_ctor_get(v_b_1000_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_b_1000_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_b_1000_, 0);
lean_dec(v_unused_1030_);
v___x_1021_ = v_b_1000_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snd_1019_);
lean_dec(v_b_1000_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1023_ = lean_array_uget_borrowed(v_as_997_, v_i_998_);
lean_inc(v___x_1023_);
v___x_1024_ = lean_array_push(v_snd_1019_, v___x_1023_);
v___x_1025_ = lean_box(v___x_1006_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___x_1024_);
lean_ctor_set(v___x_1021_, 0, v___x_1025_);
v___x_1027_ = v___x_1021_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1024_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
v___y_1002_ = v___x_1027_;
goto v___jp_1001_;
}
}
}
}
else
{
return v_b_1000_;
}
v___jp_1001_:
{
size_t v___x_1003_; size_t v___x_1004_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_998_, v___x_1003_);
v_i_998_ = v___x_1004_;
v_b_1000_ = v___y_1002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1031_, lean_object* v_as_1032_, lean_object* v_i_1033_, lean_object* v_stop_1034_, lean_object* v_b_1035_){
_start:
{
uint8_t v___x_12445__boxed_1036_; size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; lean_object* v_res_1039_; 
v___x_12445__boxed_1036_ = lean_unbox(v___x_1031_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1034_);
lean_dec(v_stop_1034_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_12445__boxed_1036_, v_as_1032_, v_i_boxed_1037_, v_stop_boxed_1038_, v_b_1035_);
lean_dec_ref(v_as_1032_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_elts_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1112_; lean_object* v_cfg_1126_; 
v_cfg_1126_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1068_) == 1)
{
lean_object* v_val_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_val_1127_ = lean_ctor_get(v_spec_x3f_1068_, 0);
lean_inc_n(v_val_1127_, 2);
lean_dec_ref(v_spec_x3f_1068_);
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1129_ = l_Lean_Syntax_isOfKind(v_val_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_val_1127_);
v___x_1130_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = l_Lean_Syntax_getArg(v_val_1127_, v___x_1139_);
lean_dec(v_val_1127_);
v___x_1141_ = l_Lean_Syntax_getArgs(v___x_1140_);
lean_dec(v___x_1140_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1144_ = lean_array_get_size(v___x_1141_);
v___x_1145_ = lean_nat_dec_lt(v___x_1142_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec_ref(v___x_1141_);
v___y_1112_ = v___x_1143_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_box(v___x_1129_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1143_);
v___x_1148_ = lean_nat_dec_le(v___x_1144_, v___x_1144_);
if (v___x_1148_ == 0)
{
if (v___x_1145_ == 0)
{
lean_dec_ref(v___x_1147_);
lean_dec_ref(v___x_1141_);
v___y_1112_ = v___x_1143_;
goto v___jp_1111_;
}
else
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v_snd_1152_; 
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = lean_usize_of_nat(v___x_1144_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1129_, v___x_1141_, v___x_1149_, v___x_1150_, v___x_1147_);
lean_dec_ref(v___x_1141_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
lean_dec_ref(v___x_1151_);
v___y_1112_ = v_snd_1152_;
goto v___jp_1111_;
}
}
else
{
size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v_snd_1156_; 
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = lean_usize_of_nat(v___x_1144_);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1129_, v___x_1141_, v___x_1153_, v___x_1154_, v___x_1147_);
lean_dec_ref(v___x_1141_);
v_snd_1156_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_snd_1156_);
lean_dec_ref(v___x_1155_);
v___y_1112_ = v_snd_1156_;
goto v___jp_1111_;
}
}
}
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_spec_x3f_1068_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_cfg_1126_);
return v___x_1157_;
}
v___jp_1072_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1076_ = l_Array_reverse___redArg(v_elts_1073_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1078_ = lean_array_size(v___x_1076_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1076_, v_sz_1078_, v___x_1079_, v___x_1077_, v___y_1074_, v___y_1075_);
lean_dec_ref(v___x_1076_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1102_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1102_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1102_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_snd_1085_; lean_object* v_snd_1086_; lean_object* v_snd_1087_; lean_object* v_fst_1088_; lean_object* v_fst_1089_; lean_object* v_fst_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___y_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1100_; 
v_snd_1085_ = lean_ctor_get(v_a_1081_, 1);
lean_inc(v_snd_1085_);
v_snd_1086_ = lean_ctor_get(v_snd_1085_, 1);
lean_inc(v_snd_1086_);
v_snd_1087_ = lean_ctor_get(v_snd_1086_, 1);
lean_inc(v_snd_1087_);
v_fst_1088_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_fst_1088_);
lean_dec(v_a_1081_);
v_fst_1089_ = lean_ctor_get(v_snd_1085_, 0);
lean_inc(v_fst_1089_);
lean_dec(v_snd_1085_);
v_fst_1090_ = lean_ctor_get(v_snd_1086_, 0);
lean_inc(v_fst_1090_);
lean_dec(v_snd_1086_);
v_fst_1091_ = lean_ctor_get(v_snd_1087_, 0);
lean_inc(v_fst_1091_);
v_snd_1092_ = lean_ctor_get(v_snd_1087_, 1);
lean_inc(v_snd_1092_);
lean_dec(v_snd_1087_);
v___y_1093_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1093_, 0, v_snd_1092_);
v___x_1094_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1094_, 0, v___y_1093_);
v___x_1095_ = lean_unbox(v_fst_1088_);
lean_dec(v_fst_1088_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1, v___x_1095_);
v___x_1096_ = lean_unbox(v_fst_1089_);
lean_dec(v_fst_1089_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1 + 1, v___x_1096_);
v___x_1097_ = lean_unbox(v_fst_1090_);
lean_dec(v_fst_1090_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1 + 2, v___x_1097_);
v___x_1098_ = lean_unbox(v_fst_1091_);
lean_dec(v_fst_1091_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1 + 3, v___x_1098_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1094_);
v___x_1100_ = v___x_1083_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1094_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1080_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1080_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
v___jp_1111_:
{
size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v_sz_1113_ = lean_array_size(v___y_1112_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1113_, v___x_1114_, v___y_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v___x_1116_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_val_1125_; 
v_val_1125_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1125_);
lean_dec_ref(v___x_1115_);
v_elts_1073_ = v_val_1125_;
v___y_1074_ = v_a_1069_;
v___y_1075_ = v_a_1070_;
goto v___jp_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1175_, lean_object* v_replacement_1176_, lean_object* v_a_1177_, lean_object* v_b_1178_){
_start:
{
lean_object* v_it_1180_; lean_object* v_startPos_1181_; lean_object* v_endPos_1182_; lean_object* v_it_1191_; 
switch(lean_obj_tag(v_a_1177_))
{
case 0:
{
lean_object* v_pos_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1209_; 
v_pos_1197_ = lean_ctor_get(v_a_1177_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1199_ = v_a_1177_;
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_pos_1197_);
lean_dec(v_a_1177_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_startInclusive_1201_; lean_object* v_endExclusive_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_startInclusive_1201_ = lean_ctor_get(v_s_1175_, 1);
v_endExclusive_1202_ = lean_ctor_get(v_s_1175_, 2);
v___x_1203_ = lean_nat_sub(v_endExclusive_1202_, v_startInclusive_1201_);
v___x_1204_ = lean_nat_dec_eq(v_pos_1197_, v___x_1203_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1206_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set_tag(v___x_1199_, 1);
v___x_1206_ = v___x_1199_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_pos_1197_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
v_it_1191_ = v___x_1206_;
goto v___jp_1190_;
}
}
else
{
lean_object* v___x_1208_; 
lean_del_object(v___x_1199_);
lean_dec(v_pos_1197_);
v___x_1208_ = lean_box(3);
v_it_1191_ = v___x_1208_;
goto v___jp_1190_;
}
}
}
case 1:
{
lean_object* v_pos_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1222_; 
v_pos_1210_ = lean_ctor_get(v_a_1177_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1212_ = v_a_1177_;
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_pos_1210_);
lean_dec(v_a_1177_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_str_1214_; lean_object* v_startInclusive_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v_str_1214_ = lean_ctor_get(v_s_1175_, 0);
v_startInclusive_1215_ = lean_ctor_get(v_s_1175_, 1);
v___x_1216_ = lean_nat_add(v_startInclusive_1215_, v_pos_1210_);
v___x_1217_ = lean_string_utf8_next_fast(v_str_1214_, v___x_1216_);
lean_dec(v___x_1216_);
v___x_1218_ = lean_nat_sub(v___x_1217_, v_startInclusive_1215_);
lean_inc(v___x_1218_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1218_);
v___x_1220_ = v___x_1212_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v_it_1180_ = v___x_1220_;
v_startPos_1181_ = v_pos_1210_;
v_endPos_1182_ = v___x_1218_;
goto v___jp_1179_;
}
}
}
case 2:
{
lean_object* v_needle_1223_; lean_object* v_table_1224_; lean_object* v_stackPos_1225_; lean_object* v_needlePos_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1285_; 
v_needle_1223_ = lean_ctor_get(v_a_1177_, 0);
v_table_1224_ = lean_ctor_get(v_a_1177_, 1);
v_stackPos_1225_ = lean_ctor_get(v_a_1177_, 2);
v_needlePos_1226_ = lean_ctor_get(v_a_1177_, 3);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1228_ = v_a_1177_;
v_isShared_1229_ = v_isSharedCheck_1285_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_needlePos_1226_);
lean_inc(v_stackPos_1225_);
lean_inc(v_table_1224_);
lean_inc(v_needle_1223_);
lean_dec(v_a_1177_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1285_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_str_1230_; lean_object* v_startInclusive_1231_; lean_object* v_endExclusive_1232_; lean_object* v_str_1233_; lean_object* v_startInclusive_1234_; lean_object* v_endExclusive_1235_; lean_object* v_basePos_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_str_1230_ = lean_ctor_get(v_needle_1223_, 0);
v_startInclusive_1231_ = lean_ctor_get(v_needle_1223_, 1);
v_endExclusive_1232_ = lean_ctor_get(v_needle_1223_, 2);
v_str_1233_ = lean_ctor_get(v_s_1175_, 0);
v_startInclusive_1234_ = lean_ctor_get(v_s_1175_, 1);
v_endExclusive_1235_ = lean_ctor_get(v_s_1175_, 2);
v_basePos_1236_ = lean_nat_sub(v_stackPos_1225_, v_needlePos_1226_);
v___x_1237_ = lean_nat_sub(v_endExclusive_1232_, v_startInclusive_1231_);
v___x_1238_ = lean_nat_add(v_basePos_1236_, v___x_1237_);
v___x_1239_ = lean_nat_sub(v_endExclusive_1235_, v_startInclusive_1234_);
v___x_1240_ = lean_nat_dec_le(v___x_1238_, v___x_1239_);
lean_dec(v___x_1238_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; 
lean_dec(v___x_1237_);
lean_del_object(v___x_1228_);
lean_dec(v_needlePos_1226_);
lean_dec(v_stackPos_1225_);
lean_dec_ref(v_table_1224_);
lean_dec_ref(v_needle_1223_);
v___x_1241_ = lean_nat_dec_lt(v_basePos_1236_, v___x_1239_);
if (v___x_1241_ == 0)
{
lean_dec(v___x_1239_);
lean_dec(v_basePos_1236_);
lean_dec_ref(v_s_1175_);
return v_b_1178_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = l_String_Slice_pos_x21(v_s_1175_, v_basePos_1236_);
lean_dec(v_basePos_1236_);
v___x_1243_ = lean_box(3);
v_it_1180_ = v___x_1243_;
v_startPos_1181_ = v___x_1242_;
v_endPos_1182_ = v___x_1239_;
goto v___jp_1179_;
}
}
else
{
lean_object* v___x_1244_; uint8_t v_stackByte_1245_; lean_object* v___x_1246_; uint8_t v_patByte_1247_; uint8_t v___x_1248_; 
lean_dec(v___x_1239_);
v___x_1244_ = lean_nat_add(v_startInclusive_1234_, v_stackPos_1225_);
v_stackByte_1245_ = lean_string_get_byte_fast(v_str_1233_, v___x_1244_);
v___x_1246_ = lean_nat_add(v_startInclusive_1231_, v_needlePos_1226_);
v_patByte_1247_ = lean_string_get_byte_fast(v_str_1230_, v___x_1246_);
v___x_1248_ = lean_uint8_dec_eq(v_stackByte_1245_, v_patByte_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
lean_dec(v___x_1237_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_nat_dec_eq(v_needlePos_1226_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_newNeedlePos_1253_; uint8_t v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_sub(v_needlePos_1226_, v___x_1251_);
lean_dec(v_needlePos_1226_);
v_newNeedlePos_1253_ = lean_array_fget_borrowed(v_table_1224_, v___x_1252_);
lean_dec(v___x_1252_);
v___x_1254_ = lean_nat_dec_eq(v_newNeedlePos_1253_, v___x_1249_);
if (v___x_1254_ == 0)
{
lean_object* v_oldBasePos_1255_; lean_object* v___x_1256_; lean_object* v_newBasePos_1257_; lean_object* v___x_1259_; 
lean_inc(v_newNeedlePos_1253_);
v_oldBasePos_1255_ = l_String_Slice_pos_x21(v_s_1175_, v_basePos_1236_);
lean_dec(v_basePos_1236_);
v___x_1256_ = lean_nat_sub(v_stackPos_1225_, v_newNeedlePos_1253_);
v_newBasePos_1257_ = l_String_Slice_pos_x21(v_s_1175_, v___x_1256_);
lean_dec(v___x_1256_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v_newNeedlePos_1253_);
v___x_1259_ = v___x_1228_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_needle_1223_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_table_1224_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_stackPos_1225_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_newNeedlePos_1253_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_it_1180_ = v___x_1259_;
v_startPos_1181_ = v_oldBasePos_1255_;
v_endPos_1182_ = v_newBasePos_1257_;
goto v___jp_1179_;
}
}
else
{
lean_object* v_basePos_1261_; lean_object* v_nextStackPos_1262_; lean_object* v___x_1264_; 
v_basePos_1261_ = l_String_Slice_pos_x21(v_s_1175_, v_basePos_1236_);
lean_dec(v_basePos_1236_);
v_nextStackPos_1262_ = l_String_Slice_posGE___redArg(v_s_1175_, v_stackPos_1225_);
lean_inc(v_nextStackPos_1262_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v___x_1249_);
lean_ctor_set(v___x_1228_, 2, v_nextStackPos_1262_);
v___x_1264_ = v___x_1228_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_needle_1223_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_table_1224_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_nextStackPos_1262_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v___x_1249_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_it_1180_ = v___x_1264_;
v_startPos_1181_ = v_basePos_1261_;
v_endPos_1182_ = v_nextStackPos_1262_;
goto v___jp_1179_;
}
}
}
else
{
lean_object* v_basePos_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_nextStackPos_1269_; lean_object* v___x_1271_; 
lean_dec(v_basePos_1236_);
lean_dec(v_needlePos_1226_);
v_basePos_1266_ = l_String_Slice_pos_x21(v_s_1175_, v_stackPos_1225_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_add(v_stackPos_1225_, v___x_1267_);
lean_dec(v_stackPos_1225_);
v_nextStackPos_1269_ = l_String_Slice_posGE___redArg(v_s_1175_, v___x_1268_);
lean_inc(v_nextStackPos_1269_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v___x_1249_);
lean_ctor_set(v___x_1228_, 2, v_nextStackPos_1269_);
v___x_1271_ = v___x_1228_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_needle_1223_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_table_1224_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_nextStackPos_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___x_1249_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v_it_1180_ = v___x_1271_;
v_startPos_1181_ = v_basePos_1266_;
v_endPos_1182_ = v_nextStackPos_1269_;
goto v___jp_1179_;
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v_nextStackPos_1274_; lean_object* v_nextNeedlePos_1275_; uint8_t v___x_1276_; 
lean_dec(v_basePos_1236_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1274_ = lean_nat_add(v_stackPos_1225_, v___x_1273_);
lean_dec(v_stackPos_1225_);
v_nextNeedlePos_1275_ = lean_nat_add(v_needlePos_1226_, v___x_1273_);
lean_dec(v_needlePos_1226_);
v___x_1276_ = lean_nat_dec_eq(v_nextNeedlePos_1275_, v___x_1237_);
lean_dec(v___x_1237_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1278_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v_nextNeedlePos_1275_);
lean_ctor_set(v___x_1228_, 2, v_nextStackPos_1274_);
v___x_1278_ = v___x_1228_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_needle_1223_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_table_1224_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_nextStackPos_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_nextNeedlePos_1275_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v_a_1177_ = v___x_1278_;
goto _start;
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec(v_nextNeedlePos_1275_);
v___x_1281_ = lean_unsigned_to_nat(0u);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v___x_1281_);
lean_ctor_set(v___x_1228_, 2, v_nextStackPos_1274_);
v___x_1283_ = v___x_1228_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_needle_1223_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_table_1224_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_nextStackPos_1274_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v_it_1191_ = v___x_1283_;
goto v___jp_1190_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1175_);
return v_b_1178_;
}
}
v___jp_1179_:
{
lean_object* v___x_1183_; lean_object* v_str_1184_; lean_object* v_startInclusive_1185_; lean_object* v_endExclusive_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_inc_ref(v_s_1175_);
v___x_1183_ = l_String_Slice_slice_x21(v_s_1175_, v_startPos_1181_, v_endPos_1182_);
lean_dec(v_endPos_1182_);
lean_dec(v_startPos_1181_);
v_str_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_str_1184_);
v_startInclusive_1185_ = lean_ctor_get(v___x_1183_, 1);
lean_inc(v_startInclusive_1185_);
v_endExclusive_1186_ = lean_ctor_get(v___x_1183_, 2);
lean_inc(v_endExclusive_1186_);
lean_dec_ref(v___x_1183_);
v___x_1187_ = lean_string_utf8_extract(v_str_1184_, v_startInclusive_1185_, v_endExclusive_1186_);
lean_dec(v_endExclusive_1186_);
lean_dec(v_startInclusive_1185_);
lean_dec_ref(v_str_1184_);
v___x_1188_ = lean_string_append(v_b_1178_, v___x_1187_);
lean_dec_ref(v___x_1187_);
v_a_1177_ = v_it_1180_;
v_b_1178_ = v___x_1188_;
goto _start;
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_string_utf8_byte_size(v_replacement_1176_);
v___x_1194_ = lean_string_utf8_extract(v_replacement_1176_, v___x_1192_, v___x_1193_);
v___x_1195_ = lean_string_append(v_b_1178_, v___x_1194_);
lean_dec_ref(v___x_1194_);
v_a_1177_ = v_it_1191_;
v_b_1178_ = v___x_1195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1286_, lean_object* v_replacement_1287_, lean_object* v_a_1288_, lean_object* v_b_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1286_, v_replacement_1287_, v_a_1288_, v_b_1289_);
lean_dec_ref(v_replacement_1287_);
return v_res_1290_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1293_ = lean_string_utf8_byte_size(v___x_1292_);
return v___x_1293_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1296_ = lean_nat_dec_eq(v___x_1295_, v___x_1294_);
return v___x_1296_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v___x_1297_);
return v___x_1300_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1302_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4);
v___x_1305_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1306_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1304_);
lean_ctor_set(v___x_1306_, 2, v___x_1303_);
lean_ctor_set(v___x_1306_, 3, v___x_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1309_, lean_object* v_replacement_1310_){
_start:
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1312_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5);
v___x_1314_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1309_, v_replacement_1310_, v___x_1313_, v___x_1311_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1316_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1309_, v_replacement_1310_, v___x_1315_, v___x_1311_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1317_, lean_object* v_replacement_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1317_, v_replacement_1318_);
lean_dec_ref(v_replacement_1318_);
return v_res_1319_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1322_ = lean_string_utf8_byte_size(v___x_1321_);
return v___x_1322_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1325_ = lean_nat_dec_eq(v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1326_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1327_);
lean_ctor_set(v___x_1329_, 2, v___x_1326_);
return v___x_1329_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1331_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4);
v___x_1334_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1335_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1332_);
lean_ctor_set(v___x_1335_, 3, v___x_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1336_, lean_object* v_replacement_1337_){
_start:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1339_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5);
v___x_1341_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1336_, v_replacement_1337_, v___x_1340_, v___x_1338_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1343_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1336_, v_replacement_1337_, v___x_1342_, v___x_1338_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1344_, lean_object* v_replacement_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1344_, v_replacement_1345_);
lean_dec_ref(v_replacement_1345_);
return v_res_1346_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1349_ = lean_string_utf8_byte_size(v___x_1348_);
return v___x_1349_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1352_ = lean_nat_dec_eq(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1353_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v___x_1354_);
lean_ctor_set(v___x_1356_, 2, v___x_1353_);
return v___x_1356_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1358_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4);
v___x_1361_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1362_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___x_1360_);
lean_ctor_set(v___x_1362_, 2, v___x_1359_);
lean_ctor_set(v___x_1362_, 3, v___x_1359_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1363_, lean_object* v_replacement_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1366_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5);
v___x_1368_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1363_, v_replacement_1364_, v___x_1367_, v___x_1365_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1370_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1363_, v_replacement_1364_, v___x_1369_, v___x_1365_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1371_, lean_object* v_replacement_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1371_, v_replacement_1372_);
lean_dec_ref(v_replacement_1372_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1378_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_string_utf8_byte_size(v_s_1377_);
v___x_1381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1381_, 0, v_s_1377_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
v___x_1382_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1381_, v___x_1378_);
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1384_ = lean_string_utf8_byte_size(v___x_1382_);
v___x_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1382_);
lean_ctor_set(v___x_1385_, 1, v___x_1379_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v___x_1386_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1385_, v___x_1383_);
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1388_ = lean_string_utf8_byte_size(v___x_1386_);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1386_);
lean_ctor_set(v___x_1389_, 1, v___x_1379_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1389_, v___x_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1391_, lean_object* v_pattern_1392_, lean_object* v_replacement_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1391_, v_replacement_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1395_, lean_object* v_pattern_1396_, lean_object* v_replacement_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1395_, v_pattern_1396_, v_replacement_1397_);
lean_dec_ref(v_replacement_1397_);
lean_dec_ref(v_pattern_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1399_, lean_object* v_pattern_1400_, lean_object* v_replacement_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1399_, v_replacement_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1403_, lean_object* v_pattern_1404_, lean_object* v_replacement_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1403_, v_pattern_1404_, v_replacement_1405_);
lean_dec_ref(v_replacement_1405_);
lean_dec_ref(v_pattern_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1407_, lean_object* v_pattern_1408_, lean_object* v_replacement_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1407_, v_replacement_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1411_, lean_object* v_pattern_1412_, lean_object* v_replacement_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1411_, v_pattern_1412_, v_replacement_1413_);
lean_dec_ref(v_replacement_1413_);
lean_dec_ref(v_pattern_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1415_, lean_object* v_replacement_1416_, lean_object* v_inst_1417_, lean_object* v_R_1418_, lean_object* v_a_1419_, lean_object* v_b_1420_, lean_object* v_c_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1415_, v_replacement_1416_, v_a_1419_, v_b_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1423_, lean_object* v_replacement_1424_, lean_object* v_inst_1425_, lean_object* v_R_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v_c_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1423_, v_replacement_1424_, v_inst_1425_, v_R_1426_, v_a_1427_, v_b_1428_, v_c_1429_);
lean_dec_ref(v_replacement_1424_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1432_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_string_utf8_byte_size(v_s_1431_);
v___x_1435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1435_, 0, v_s_1431_);
lean_ctor_set(v___x_1435_, 1, v___x_1433_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
v___x_1436_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1435_, v___x_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0));
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1441_);
lean_dec_ref(v_s_1441_);
return v_res_1442_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1445_ = lean_nat_dec_eq(v___x_1444_, v___x_1443_);
return v___x_1445_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1446_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v___x_1447_);
lean_ctor_set(v___x_1449_, 2, v___x_1446_);
return v___x_1449_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1451_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1454_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1455_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1453_);
lean_ctor_set(v___x_1455_, 2, v___x_1452_);
lean_ctor_set(v___x_1455_, 3, v___x_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1456_, lean_object* v_replacement_1457_){
_start:
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1459_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1461_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1456_, v_replacement_1457_, v___x_1460_, v___x_1458_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1463_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1456_, v_replacement_1457_, v___x_1462_, v___x_1458_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1464_, lean_object* v_replacement_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1464_, v_replacement_1465_);
lean_dec_ref(v_replacement_1465_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1467_, lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v_a_1470_, lean_object* v_b_1471_){
_start:
{
lean_object* v_it_1473_; lean_object* v_startInclusive_1474_; lean_object* v_endExclusive_1475_; 
if (lean_obj_tag(v_a_1470_) == 0)
{
lean_object* v_currPos_1483_; lean_object* v_searcher_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1519_; 
v_currPos_1483_ = lean_ctor_get(v_a_1470_, 0);
v_searcher_1484_ = lean_ctor_get(v_a_1470_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1470_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1486_ = v_a_1470_;
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_searcher_1484_);
lean_inc(v_currPos_1483_);
lean_dec(v_a_1470_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint8_t v___y_1499_; lean_object* v_startInclusive_1503_; lean_object* v_endExclusive_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_startInclusive_1503_ = lean_ctor_get(v___x_1468_, 1);
v_endExclusive_1504_ = lean_ctor_get(v___x_1468_, 2);
v___x_1505_ = lean_nat_sub(v_endExclusive_1504_, v_startInclusive_1503_);
v___x_1506_ = lean_nat_dec_eq(v_searcher_1484_, v___x_1505_);
lean_dec(v___x_1505_);
if (v___x_1506_ == 0)
{
uint32_t v___x_1507_; uint8_t v___y_1509_; uint32_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1507_ = lean_string_utf8_get_fast(v_s_1467_, v_searcher_1484_);
v___x_1514_ = 32;
v___x_1515_ = lean_uint32_dec_eq(v___x_1507_, v___x_1514_);
if (v___x_1515_ == 0)
{
uint32_t v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = 9;
v___x_1517_ = lean_uint32_dec_eq(v___x_1507_, v___x_1516_);
v___y_1509_ = v___x_1517_;
goto v___jp_1508_;
}
else
{
v___y_1509_ = v___x_1515_;
goto v___jp_1508_;
}
v___jp_1508_:
{
if (v___y_1509_ == 0)
{
uint32_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = 13;
v___x_1511_ = lean_uint32_dec_eq(v___x_1507_, v___x_1510_);
if (v___x_1511_ == 0)
{
uint32_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = 10;
v___x_1513_ = lean_uint32_dec_eq(v___x_1507_, v___x_1512_);
v___y_1499_ = v___x_1513_;
goto v___jp_1498_;
}
else
{
v___y_1499_ = v___x_1511_;
goto v___jp_1498_;
}
}
else
{
goto v___jp_1488_;
}
}
}
else
{
lean_object* v___x_1518_; 
lean_del_object(v___x_1486_);
lean_dec(v_searcher_1484_);
v___x_1518_ = lean_box(1);
lean_inc(v___x_1469_);
v_it_1473_ = v___x_1518_;
v_startInclusive_1474_ = v_currPos_1483_;
v_endExclusive_1475_ = v___x_1469_;
goto v___jp_1472_;
}
v___jp_1488_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_slice_1492_; lean_object* v_nextIt_1494_; 
v___x_1489_ = lean_string_utf8_next_fast(v_s_1467_, v_searcher_1484_);
v___x_1490_ = lean_nat_sub(v___x_1489_, v_searcher_1484_);
v___x_1491_ = lean_nat_add(v_searcher_1484_, v___x_1490_);
lean_dec(v___x_1490_);
v_slice_1492_ = l_String_Slice_subslice_x21(v___x_1468_, v_currPos_1483_, v_searcher_1484_);
lean_inc(v___x_1491_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1491_);
lean_ctor_set(v___x_1486_, 0, v___x_1491_);
v_nextIt_1494_ = v___x_1486_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1491_);
v_nextIt_1494_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v_startInclusive_1495_; lean_object* v_endExclusive_1496_; 
v_startInclusive_1495_ = lean_ctor_get(v_slice_1492_, 0);
lean_inc(v_startInclusive_1495_);
v_endExclusive_1496_ = lean_ctor_get(v_slice_1492_, 1);
lean_inc(v_endExclusive_1496_);
lean_dec_ref(v_slice_1492_);
v_it_1473_ = v_nextIt_1494_;
v_startInclusive_1474_ = v_startInclusive_1495_;
v_endExclusive_1475_ = v_endExclusive_1496_;
goto v___jp_1472_;
}
}
v___jp_1498_:
{
if (v___y_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_del_object(v___x_1486_);
v___x_1500_ = lean_string_utf8_next_fast(v_s_1467_, v_searcher_1484_);
lean_dec(v_searcher_1484_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_currPos_1483_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v_a_1470_ = v___x_1501_;
goto _start;
}
else
{
goto v___jp_1488_;
}
}
}
}
else
{
lean_dec(v___x_1469_);
lean_dec_ref(v_s_1467_);
return v_b_1471_;
}
v___jp_1472_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_nat_sub(v_endExclusive_1475_, v_startInclusive_1474_);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_nat_dec_eq(v___x_1476_, v___x_1477_);
lean_dec(v___x_1476_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_inc_ref(v_s_1467_);
v___x_1479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1479_, 0, v_s_1467_);
lean_ctor_set(v___x_1479_, 1, v_startInclusive_1474_);
lean_ctor_set(v___x_1479_, 2, v_endExclusive_1475_);
v___x_1480_ = lean_array_push(v_b_1471_, v___x_1479_);
v_a_1470_ = v_it_1473_;
v_b_1471_ = v___x_1480_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1475_);
lean_dec(v_startInclusive_1474_);
v_a_1470_ = v_it_1473_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1520_, lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v_a_1523_, lean_object* v_b_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1520_, v___x_1521_, v___x_1522_, v_a_1523_, v_b_1524_);
lean_dec_ref(v___x_1521_);
return v_res_1525_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1527_ = lean_string_utf8_byte_size(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1529_);
lean_ctor_set(v___x_1531_, 2, v___x_1528_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1534_, lean_object* v_s_1535_){
_start:
{
switch(v_mode_1534_)
{
case 0:
{
return v_s_1535_;
}
case 1:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1536_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_string_utf8_byte_size(v_s_1535_);
v___x_1539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1539_, 0, v_s_1535_);
lean_ctor_set(v___x_1539_, 1, v___x_1537_);
lean_ctor_set(v___x_1539_, 2, v___x_1538_);
v___x_1540_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1539_, v___x_1536_);
return v___x_1540_;
}
default: 
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1);
v___x_1543_ = lean_string_utf8_byte_size(v_s_1535_);
lean_inc_ref(v_s_1535_);
v___x_1544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1544_, 0, v_s_1535_);
lean_ctor_set(v___x_1544_, 1, v___x_1541_);
lean_ctor_set(v___x_1544_, 2, v___x_1543_);
v___x_1545_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v___x_1544_);
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2));
v___x_1547_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1535_, v___x_1544_, v___x_1543_, v___x_1545_, v___x_1546_);
lean_dec_ref(v___x_1544_);
v___x_1548_ = lean_array_to_list(v___x_1547_);
v___x_1549_ = l_String_Slice_intercalate(v___x_1542_, v___x_1548_);
lean_dec(v___x_1548_);
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1550_, lean_object* v_s_1551_){
_start:
{
uint8_t v_mode_boxed_1552_; lean_object* v_res_1553_; 
v_mode_boxed_1552_ = lean_unbox(v_mode_1550_);
v_res_1553_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1552_, v_s_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1554_, lean_object* v_pattern_1555_, lean_object* v_replacement_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1554_, v_replacement_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1558_, lean_object* v_pattern_1559_, lean_object* v_replacement_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1558_, v_pattern_1559_, v_replacement_1560_);
lean_dec_ref(v_replacement_1560_);
lean_dec_ref(v_pattern_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1562_, lean_object* v___x_1563_, lean_object* v___x_1564_, lean_object* v_inst_1565_, lean_object* v_R_1566_, lean_object* v_a_1567_, lean_object* v_b_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1562_, v___x_1563_, v___x_1564_, v_a_1567_, v_b_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v_inst_1573_, lean_object* v_R_1574_, lean_object* v_a_1575_, lean_object* v_b_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1570_, v___x_1571_, v___x_1572_, v_inst_1573_, v_R_1574_, v_a_1575_, v_b_1576_);
lean_dec_ref(v___x_1571_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1578_, lean_object* v_pivot_1579_, lean_object* v_as_1580_, lean_object* v_i_1581_, lean_object* v_k_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_lt(v_k_1582_, v_hi_1578_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v_k_1582_);
v___x_1584_ = lean_array_fswap(v_as_1580_, v_i_1581_, v_hi_1578_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_i_1581_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_array_fget_borrowed(v_as_1580_, v_k_1582_);
v___x_1587_ = lean_string_dec_lt(v___x_1586_, v_pivot_1579_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_unsigned_to_nat(1u);
v___x_1589_ = lean_nat_add(v_k_1582_, v___x_1588_);
lean_dec(v_k_1582_);
v_k_1582_ = v___x_1589_;
goto _start;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = lean_array_fswap(v_as_1580_, v_i_1581_, v_k_1582_);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_add(v_i_1581_, v___x_1592_);
lean_dec(v_i_1581_);
v___x_1594_ = lean_nat_add(v_k_1582_, v___x_1592_);
lean_dec(v_k_1582_);
v_as_1580_ = v___x_1591_;
v_i_1581_ = v___x_1593_;
v_k_1582_ = v___x_1594_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1596_, lean_object* v_pivot_1597_, lean_object* v_as_1598_, lean_object* v_i_1599_, lean_object* v_k_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1596_, v_pivot_1597_, v_as_1598_, v_i_1599_, v_k_1600_);
lean_dec_ref(v_pivot_1597_);
lean_dec(v_hi_1596_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1602_, lean_object* v_as_1603_, lean_object* v_lo_1604_, lean_object* v_hi_1605_){
_start:
{
lean_object* v___y_1607_; uint8_t v___x_1617_; 
v___x_1617_ = lean_nat_dec_lt(v_lo_1604_, v_hi_1605_);
if (v___x_1617_ == 0)
{
lean_dec(v_lo_1604_);
return v_as_1603_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v_mid_1620_; lean_object* v___y_1622_; lean_object* v___y_1628_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1618_ = lean_nat_add(v_lo_1604_, v_hi_1605_);
v___x_1619_ = lean_unsigned_to_nat(1u);
v_mid_1620_ = lean_nat_shiftr(v___x_1618_, v___x_1619_);
lean_dec(v___x_1618_);
v___x_1633_ = lean_array_fget_borrowed(v_as_1603_, v_mid_1620_);
v___x_1634_ = lean_array_fget_borrowed(v_as_1603_, v_lo_1604_);
v___x_1635_ = lean_string_dec_lt(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
v___y_1628_ = v_as_1603_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_array_fswap(v_as_1603_, v_lo_1604_, v_mid_1620_);
v___y_1628_ = v___x_1636_;
goto v___jp_1627_;
}
v___jp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1623_ = lean_array_fget_borrowed(v___y_1622_, v_mid_1620_);
v___x_1624_ = lean_array_fget_borrowed(v___y_1622_, v_hi_1605_);
v___x_1625_ = lean_string_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec(v_mid_1620_);
v___y_1607_ = v___y_1622_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_array_fswap(v___y_1622_, v_mid_1620_, v_hi_1605_);
lean_dec(v_mid_1620_);
v___y_1607_ = v___x_1626_;
goto v___jp_1606_;
}
}
v___jp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1629_ = lean_array_fget_borrowed(v___y_1628_, v_hi_1605_);
v___x_1630_ = lean_array_fget_borrowed(v___y_1628_, v_lo_1604_);
v___x_1631_ = lean_string_dec_lt(v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
v___y_1622_ = v___y_1628_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_array_fswap(v___y_1628_, v_lo_1604_, v_hi_1605_);
v___y_1622_ = v___x_1632_;
goto v___jp_1621_;
}
}
}
v___jp_1606_:
{
lean_object* v_pivot_1608_; lean_object* v___x_1609_; lean_object* v_fst_1610_; lean_object* v_snd_1611_; uint8_t v___x_1612_; 
v_pivot_1608_ = lean_array_fget(v___y_1607_, v_hi_1605_);
lean_inc_n(v_lo_1604_, 2);
v___x_1609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1605_, v_pivot_1608_, v___y_1607_, v_lo_1604_, v_lo_1604_);
lean_dec(v_pivot_1608_);
v_fst_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_fst_1610_);
v_snd_1611_ = lean_ctor_get(v___x_1609_, 1);
lean_inc(v_snd_1611_);
lean_dec_ref(v___x_1609_);
v___x_1612_ = lean_nat_dec_le(v_hi_1605_, v_fst_1610_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1602_, v_snd_1611_, v_lo_1604_, v_fst_1610_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v_fst_1610_, v___x_1614_);
lean_dec(v_fst_1610_);
v_as_1603_ = v___x_1613_;
v_lo_1604_ = v___x_1615_;
goto _start;
}
else
{
lean_dec(v_fst_1610_);
lean_dec(v_lo_1604_);
return v_snd_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1637_, lean_object* v_as_1638_, lean_object* v_lo_1639_, lean_object* v_hi_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1637_, v_as_1638_, v_lo_1639_, v_hi_1640_);
lean_dec(v_hi_1640_);
lean_dec(v_n_1637_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1642_, lean_object* v_msgs_1643_){
_start:
{
if (v_mode_1642_ == 0)
{
return v_msgs_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1644_ = lean_array_mk(v_msgs_1643_);
v___x_1645_ = lean_array_get_size(v___x_1644_);
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_nat_dec_eq(v___x_1645_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___y_1656_; uint8_t v___x_1658_; 
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_sub(v___x_1645_, v___x_1653_);
v___x_1658_ = lean_nat_dec_le(v___x_1651_, v___x_1654_);
if (v___x_1658_ == 0)
{
lean_inc(v___x_1654_);
v___y_1656_ = v___x_1654_;
goto v___jp_1655_;
}
else
{
v___y_1656_ = v___x_1651_;
goto v___jp_1655_;
}
v___jp_1655_:
{
uint8_t v___x_1657_; 
v___x_1657_ = lean_nat_dec_le(v___y_1656_, v___x_1654_);
if (v___x_1657_ == 0)
{
lean_dec(v___x_1654_);
lean_inc(v___y_1656_);
v___y_1647_ = v___y_1656_;
v___y_1648_ = v___y_1656_;
goto v___jp_1646_;
}
else
{
v___y_1647_ = v___y_1656_;
v___y_1648_ = v___x_1654_;
goto v___jp_1646_;
}
}
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_array_to_list(v___x_1644_);
return v___x_1659_;
}
v___jp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1645_, v___x_1644_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
v___x_1650_ = lean_array_to_list(v___x_1649_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1660_, lean_object* v_msgs_1661_){
_start:
{
uint8_t v_mode_boxed_1662_; lean_object* v_res_1663_; 
v_mode_boxed_1662_ = lean_unbox(v_mode_1660_);
v_res_1663_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1662_, v_msgs_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1664_, lean_object* v_as_1665_, lean_object* v_lo_1666_, lean_object* v_hi_1667_, lean_object* v_w_1668_, lean_object* v_hlo_1669_, lean_object* v_hhi_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1664_, v_as_1665_, v_lo_1666_, v_hi_1667_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1672_, lean_object* v_as_1673_, lean_object* v_lo_1674_, lean_object* v_hi_1675_, lean_object* v_w_1676_, lean_object* v_hlo_1677_, lean_object* v_hhi_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1672_, v_as_1673_, v_lo_1674_, v_hi_1675_, v_w_1676_, v_hlo_1677_, v_hhi_1678_);
lean_dec(v_hi_1675_);
lean_dec(v_n_1672_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1680_, lean_object* v_lo_1681_, lean_object* v_hi_1682_, lean_object* v_hhi_1683_, lean_object* v_pivot_1684_, lean_object* v_as_1685_, lean_object* v_i_1686_, lean_object* v_k_1687_, lean_object* v_ilo_1688_, lean_object* v_ik_1689_, lean_object* v_w_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1682_, v_pivot_1684_, v_as_1685_, v_i_1686_, v_k_1687_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1692_, lean_object* v_lo_1693_, lean_object* v_hi_1694_, lean_object* v_hhi_1695_, lean_object* v_pivot_1696_, lean_object* v_as_1697_, lean_object* v_i_1698_, lean_object* v_k_1699_, lean_object* v_ilo_1700_, lean_object* v_ik_1701_, lean_object* v_w_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1692_, v_lo_1693_, v_hi_1694_, v_hhi_1695_, v_pivot_1696_, v_as_1697_, v_i_1698_, v_k_1699_, v_ilo_1700_, v_ik_1701_, v_w_1702_);
lean_dec_ref(v_pivot_1696_);
lean_dec(v_hi_1694_);
lean_dec(v_lo_1693_);
lean_dec(v_n_1692_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1704_, size_t v_i_1705_, size_t v_stop_1706_, lean_object* v_b_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_eq(v_i_1705_, v_stop_1706_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v_diagnostics_1710_; lean_object* v_msgLog_1711_; lean_object* v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; 
v___x_1709_ = lean_array_uget_borrowed(v_as_1704_, v_i_1705_);
v_diagnostics_1710_ = lean_ctor_get(v___x_1709_, 1);
v_msgLog_1711_ = lean_ctor_get(v_diagnostics_1710_, 0);
lean_inc_ref(v_msgLog_1711_);
v___x_1712_ = l_Lean_MessageLog_append(v_b_1707_, v_msgLog_1711_);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1705_, v___x_1713_);
v_i_1705_ = v___x_1714_;
v_b_1707_ = v___x_1712_;
goto _start;
}
else
{
return v_b_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1716_, lean_object* v_i_1717_, lean_object* v_stop_1718_, lean_object* v_b_1719_){
_start:
{
size_t v_i_boxed_1720_; size_t v_stop_boxed_1721_; lean_object* v_res_1722_; 
v_i_boxed_1720_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_stop_boxed_1721_ = lean_unbox_usize(v_stop_1718_);
lean_dec(v_stop_1718_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1716_, v_i_boxed_1720_, v_stop_boxed_1721_, v_b_1719_);
lean_dec_ref(v_as_1716_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1723_, size_t v_i_1724_, size_t v_stop_1725_, lean_object* v_b_1726_){
_start:
{
lean_object* v___y_1728_; uint8_t v___x_1732_; 
v___x_1732_ = lean_usize_dec_eq(v_i_1724_, v_stop_1725_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1733_ = lean_array_uget_borrowed(v_as_1723_, v_i_1724_);
v___x_1734_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1733_);
v___x_1735_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1733_);
v___x_1736_ = l_Lean_Language_SnapshotTree_getAll(v___x_1735_);
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_array_get_size(v___x_1736_);
v___x_1739_ = lean_nat_dec_lt(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v___x_1736_);
v___x_1740_ = l_Lean_MessageLog_append(v_b_1726_, v___x_1734_);
v___y_1728_ = v___x_1740_;
goto v___jp_1727_;
}
else
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_le(v___x_1738_, v___x_1738_);
if (v___x_1741_ == 0)
{
if (v___x_1739_ == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v___x_1736_);
v___x_1742_ = l_Lean_MessageLog_append(v_b_1726_, v___x_1734_);
v___y_1728_ = v___x_1742_;
goto v___jp_1727_;
}
else
{
size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = lean_usize_of_nat(v___x_1738_);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1736_, v___x_1743_, v___x_1744_, v___x_1734_);
lean_dec_ref(v___x_1736_);
v___x_1746_ = l_Lean_MessageLog_append(v_b_1726_, v___x_1745_);
v___y_1728_ = v___x_1746_;
goto v___jp_1727_;
}
}
else
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = lean_usize_of_nat(v___x_1738_);
v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1736_, v___x_1747_, v___x_1748_, v___x_1734_);
lean_dec_ref(v___x_1736_);
v___x_1750_ = l_Lean_MessageLog_append(v_b_1726_, v___x_1749_);
v___y_1728_ = v___x_1750_;
goto v___jp_1727_;
}
}
}
else
{
return v_b_1726_;
}
v___jp_1727_:
{
size_t v___x_1729_; size_t v___x_1730_; 
v___x_1729_ = ((size_t)1ULL);
v___x_1730_ = lean_usize_add(v_i_1724_, v___x_1729_);
v_i_1724_ = v___x_1730_;
v_b_1726_ = v___y_1728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1751_, lean_object* v_i_1752_, lean_object* v_stop_1753_, lean_object* v_b_1754_){
_start:
{
size_t v_i_boxed_1755_; size_t v_stop_boxed_1756_; lean_object* v_res_1757_; 
v_i_boxed_1755_ = lean_unbox_usize(v_i_1752_);
lean_dec(v_i_1752_);
v_stop_boxed_1756_ = lean_unbox_usize(v_stop_1753_);
lean_dec(v_stop_1753_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1751_, v_i_boxed_1755_, v_stop_boxed_1756_, v_b_1754_);
lean_dec_ref(v_as_1751_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_fileName_1764_; lean_object* v_fileMap_1765_; lean_object* v_currRecDepth_1766_; lean_object* v_cmdPos_1767_; lean_object* v_macroStack_1768_; lean_object* v_quotContext_x3f_1769_; lean_object* v_currMacroScope_1770_; lean_object* v_ref_1771_; lean_object* v_cancelTk_x3f_1772_; uint8_t v_suppressElabErrors_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_fileName_1764_ = lean_ctor_get(v_a_1761_, 0);
v_fileMap_1765_ = lean_ctor_get(v_a_1761_, 1);
v_currRecDepth_1766_ = lean_ctor_get(v_a_1761_, 2);
v_cmdPos_1767_ = lean_ctor_get(v_a_1761_, 3);
v_macroStack_1768_ = lean_ctor_get(v_a_1761_, 4);
v_quotContext_x3f_1769_ = lean_ctor_get(v_a_1761_, 5);
v_currMacroScope_1770_ = lean_ctor_get(v_a_1761_, 6);
v_ref_1771_ = lean_ctor_get(v_a_1761_, 7);
v_cancelTk_x3f_1772_ = lean_ctor_get(v_a_1761_, 9);
v_suppressElabErrors_1773_ = lean_ctor_get_uint8(v_a_1761_, sizeof(void*)*10);
v___x_1774_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1772_);
lean_inc(v_ref_1771_);
lean_inc(v_currMacroScope_1770_);
lean_inc(v_quotContext_x3f_1769_);
lean_inc(v_macroStack_1768_);
lean_inc(v_cmdPos_1767_);
lean_inc(v_currRecDepth_1766_);
lean_inc_ref(v_fileMap_1765_);
lean_inc_ref(v_fileName_1764_);
v___x_1775_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1775_, 0, v_fileName_1764_);
lean_ctor_set(v___x_1775_, 1, v_fileMap_1765_);
lean_ctor_set(v___x_1775_, 2, v_currRecDepth_1766_);
lean_ctor_set(v___x_1775_, 3, v_cmdPos_1767_);
lean_ctor_set(v___x_1775_, 4, v_macroStack_1768_);
lean_ctor_set(v___x_1775_, 5, v_quotContext_x3f_1769_);
lean_ctor_set(v___x_1775_, 6, v_currMacroScope_1770_);
lean_ctor_set(v___x_1775_, 7, v_ref_1771_);
lean_ctor_set(v___x_1775_, 8, v___x_1774_);
lean_ctor_set(v___x_1775_, 9, v_cancelTk_x3f_1772_);
lean_ctor_set_uint8(v___x_1775_, sizeof(void*)*10, v_suppressElabErrors_1773_);
v___x_1776_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1760_, v___x_1775_, v_a_1762_);
lean_dec_ref(v___x_1775_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1822_; 
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1823_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1822_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1822_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_messages_1782_; lean_object* v___y_1784_; lean_object* v_snapshotTasks_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1780_ = lean_st_ref_get(v_a_1762_);
v___x_1781_ = lean_st_ref_get(v_a_1762_);
v_messages_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc_ref(v_messages_1782_);
lean_dec(v___x_1780_);
v_snapshotTasks_1810_ = lean_ctor_get(v___x_1781_, 10);
lean_inc_ref(v_snapshotTasks_1810_);
lean_dec(v___x_1781_);
v___x_1811_ = l_Lean_MessageLog_empty;
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_array_get_size(v_snapshotTasks_1810_);
v___x_1814_ = lean_nat_dec_lt(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v_snapshotTasks_1810_);
v___y_1784_ = v___x_1811_;
goto v___jp_1783_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_le(v___x_1813_, v___x_1813_);
if (v___x_1815_ == 0)
{
if (v___x_1814_ == 0)
{
lean_dec_ref(v_snapshotTasks_1810_);
v___y_1784_ = v___x_1811_;
goto v___jp_1783_;
}
else
{
size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1813_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1810_, v___x_1816_, v___x_1817_, v___x_1811_);
lean_dec_ref(v_snapshotTasks_1810_);
v___y_1784_ = v___x_1818_;
goto v___jp_1783_;
}
}
else
{
size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = lean_usize_of_nat(v___x_1813_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1810_, v___x_1819_, v___x_1820_, v___x_1811_);
lean_dec_ref(v_snapshotTasks_1810_);
v___y_1784_ = v___x_1821_;
goto v___jp_1783_;
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v_env_1786_; lean_object* v_messages_1787_; lean_object* v_scopes_1788_; lean_object* v_usedQuotCtxts_1789_; lean_object* v_nextMacroScope_1790_; lean_object* v_maxRecDepth_1791_; lean_object* v_ngen_1792_; lean_object* v_auxDeclNGen_1793_; lean_object* v_infoState_1794_; lean_object* v_traceState_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1808_; 
v___x_1785_ = lean_st_ref_take(v_a_1762_);
v_env_1786_ = lean_ctor_get(v___x_1785_, 0);
v_messages_1787_ = lean_ctor_get(v___x_1785_, 1);
v_scopes_1788_ = lean_ctor_get(v___x_1785_, 2);
v_usedQuotCtxts_1789_ = lean_ctor_get(v___x_1785_, 3);
v_nextMacroScope_1790_ = lean_ctor_get(v___x_1785_, 4);
v_maxRecDepth_1791_ = lean_ctor_get(v___x_1785_, 5);
v_ngen_1792_ = lean_ctor_get(v___x_1785_, 6);
v_auxDeclNGen_1793_ = lean_ctor_get(v___x_1785_, 7);
v_infoState_1794_ = lean_ctor_get(v___x_1785_, 8);
v_traceState_1795_ = lean_ctor_get(v___x_1785_, 9);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1785_, 10);
lean_dec(v_unused_1809_);
v___x_1797_ = v___x_1785_;
v_isShared_1798_ = v_isSharedCheck_1808_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_traceState_1795_);
lean_inc(v_infoState_1794_);
lean_inc(v_auxDeclNGen_1793_);
lean_inc(v_ngen_1792_);
lean_inc(v_maxRecDepth_1791_);
lean_inc(v_nextMacroScope_1790_);
lean_inc(v_usedQuotCtxts_1789_);
lean_inc(v_scopes_1788_);
lean_inc(v_messages_1787_);
lean_inc(v_env_1786_);
lean_dec(v___x_1785_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1808_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 10, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_env_1786_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_messages_1787_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_scopes_1788_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_usedQuotCtxts_1789_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_nextMacroScope_1790_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_maxRecDepth_1791_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_ngen_1792_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_auxDeclNGen_1793_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_infoState_1794_);
lean_ctor_set(v_reuseFailAlloc_1807_, 9, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1807_, 10, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = lean_st_ref_set(v_a_1762_, v___x_1801_);
v___x_1803_ = l_Lean_MessageLog_append(v_messages_1782_, v___y_1784_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1803_);
v___x_1805_ = v___x_1778_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1776_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1776_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1836_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1837_, lean_object* v_opt_1838_){
_start:
{
lean_object* v_name_1839_; lean_object* v_defValue_1840_; lean_object* v_map_1841_; lean_object* v___x_1842_; 
v_name_1839_ = lean_ctor_get(v_opt_1838_, 0);
v_defValue_1840_ = lean_ctor_get(v_opt_1838_, 1);
v_map_1841_ = lean_ctor_get(v_opts_1837_, 0);
v___x_1842_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1841_, v_name_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_unbox(v_defValue_1840_);
return v___x_1843_;
}
else
{
lean_object* v_val_1844_; 
v_val_1844_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_val_1844_);
lean_dec_ref(v___x_1842_);
if (lean_obj_tag(v_val_1844_) == 1)
{
uint8_t v_v_1845_; 
v_v_1845_ = lean_ctor_get_uint8(v_val_1844_, 0);
lean_dec_ref(v_val_1844_);
return v_v_1845_;
}
else
{
uint8_t v___x_1846_; 
lean_dec(v_val_1844_);
v___x_1846_ = lean_unbox(v_defValue_1840_);
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1847_, lean_object* v_opt_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1847_, v_opt_1848_);
lean_dec_ref(v_opt_1848_);
lean_dec_ref(v_opts_1847_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1855_);
lean_dec_ref(v_s_1855_);
return v_res_1856_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_box(1);
v___x_1858_ = l_Lean_MessageData_ofFormat(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1863_ = l_Lean_MessageData_ofFormat(v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
return v_x_1864_;
}
else
{
lean_object* v_head_1866_; lean_object* v_tail_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1889_; 
v_head_1866_ = lean_ctor_get(v_x_1865_, 0);
v_tail_1867_ = lean_ctor_get(v_x_1865_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1869_ = v_x_1865_;
v_isShared_1870_ = v_isSharedCheck_1889_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_tail_1867_);
lean_inc(v_head_1866_);
lean_dec(v_x_1865_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1889_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_before_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1887_; 
v_before_1871_ = lean_ctor_get(v_head_1866_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_head_1866_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_head_1866_, 1);
lean_dec(v_unused_1888_);
v___x_1873_ = v_head_1866_;
v_isShared_1874_ = v_isSharedCheck_1887_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_before_1871_);
lean_dec(v_head_1866_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1887_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 7);
lean_ctor_set(v___x_1873_, 1, v___x_1875_);
lean_ctor_set(v___x_1873_, 0, v_x_1864_);
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_x_1864_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 7);
lean_ctor_set(v___x_1869_, 1, v___x_1878_);
lean_ctor_set(v___x_1869_, 0, v___x_1877_);
v___x_1880_ = v___x_1869_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_MessageData_ofSyntax(v_before_1871_);
v___x_1882_ = l_Lean_indentD(v___x_1881_);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v_x_1864_ = v___x_1883_;
v_x_1865_ = v_tail_1867_;
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
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1894_ = l_Lean_MessageData_ofFormat(v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1895_, lean_object* v_macroStack_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v_scopes_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_opts_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1899_ = lean_st_ref_get(v___y_1897_);
v_scopes_1900_ = lean_ctor_get(v___x_1899_, 2);
lean_inc(v_scopes_1900_);
lean_dec(v___x_1899_);
v___x_1901_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1902_ = l_List_head_x21___redArg(v___x_1901_, v_scopes_1900_);
lean_dec(v_scopes_1900_);
v_opts_1903_ = lean_ctor_get(v___x_1902_, 1);
lean_inc_ref(v_opts_1903_);
lean_dec(v___x_1902_);
v___x_1904_ = l_Lean_Elab_pp_macroStack;
v___x_1905_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1903_, v___x_1904_);
lean_dec_ref(v_opts_1903_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec(v_macroStack_1896_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_msgData_1895_);
return v___x_1906_;
}
else
{
if (lean_obj_tag(v_macroStack_1896_) == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_msgData_1895_);
return v___x_1907_;
}
else
{
lean_object* v_head_1908_; lean_object* v_after_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1924_; 
v_head_1908_ = lean_ctor_get(v_macroStack_1896_, 0);
lean_inc(v_head_1908_);
v_after_1909_ = lean_ctor_get(v_head_1908_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_head_1908_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v_head_1908_, 0);
lean_dec(v_unused_1925_);
v___x_1911_ = v_head_1908_;
v_isShared_1912_ = v_isSharedCheck_1924_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_after_1909_);
lean_dec(v_head_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1924_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 7);
lean_ctor_set(v___x_1911_, 1, v___x_1913_);
lean_ctor_set(v___x_1911_, 0, v_msgData_1895_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_msgData_1895_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_msgData_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1916_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_MessageData_ofSyntax(v_after_1909_);
v___x_1919_ = l_Lean_indentD(v___x_1918_);
v_msgData_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1920_, 0, v___x_1917_);
lean_ctor_set(v_msgData_1920_, 1, v___x_1919_);
v___x_1921_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1920_, v_macroStack_1896_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1926_, lean_object* v_macroStack_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1926_, v_macroStack_1927_, v___y_1928_);
lean_dec(v___y_1928_);
return v_res_1930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
lean_ctor_set(v___x_1936_, 2, v___x_1935_);
lean_ctor_set(v___x_1936_, 3, v___x_1935_);
lean_ctor_set(v___x_1936_, 4, v___x_1934_);
lean_ctor_set(v___x_1936_, 5, v___x_1934_);
lean_ctor_set(v___x_1936_, 6, v___x_1934_);
lean_ctor_set(v___x_1936_, 7, v___x_1934_);
lean_ctor_set(v___x_1936_, 8, v___x_1934_);
lean_ctor_set(v___x_1936_, 9, v___x_1934_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(32u);
v___x_1938_ = lean_mk_empty_array_with_capacity(v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = ((size_t)5ULL);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_unsigned_to_nat(32u);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
v___x_1944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1945_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1943_);
lean_ctor_set(v___x_1945_, 2, v___x_1941_);
lean_ctor_set(v___x_1945_, 3, v___x_1941_);
lean_ctor_set_usize(v___x_1945_, 4, v___x_1940_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = lean_box(1);
v___x_1947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1947_);
lean_ctor_set(v___x_1949_, 2, v___x_1946_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v_env_1954_; lean_object* v___x_1955_; lean_object* v_scopes_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v_opts_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1953_ = lean_st_ref_get(v___y_1951_);
v_env_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc_ref(v_env_1954_);
lean_dec(v___x_1953_);
v___x_1955_ = lean_st_ref_get(v___y_1951_);
v_scopes_1956_ = lean_ctor_get(v___x_1955_, 2);
lean_inc(v_scopes_1956_);
lean_dec(v___x_1955_);
v___x_1957_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1958_ = l_List_head_x21___redArg(v___x_1957_, v_scopes_1956_);
lean_dec(v_scopes_1956_);
v_opts_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc_ref(v_opts_1959_);
lean_dec(v___x_1958_);
v___x_1960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1961_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1962_, 0, v_env_1954_);
lean_ctor_set(v___x_1962_, 1, v___x_1960_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
lean_ctor_set(v___x_1962_, 3, v_opts_1959_);
v___x_1963_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v_msgData_1950_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1965_, v___y_1966_);
lean_dec(v___y_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Elab_Command_getRef___redArg(v___y_1970_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_macroStack_1975_; lean_object* v___x_1976_; lean_object* v_a_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v_macroStack_1975_ = lean_ctor_get(v___y_1970_, 4);
v___x_1976_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1969_, v___y_1971_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_Elab_getBetterRef(v_a_1974_, v_macroStack_1975_);
lean_dec(v_a_1974_);
lean_inc(v_macroStack_1975_);
v___x_1979_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1977_, v_macroStack_1975_, v___y_1971_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1978_);
lean_ctor_set(v___x_1984_, 1, v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 1);
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v_msg_1969_);
v_a_1989_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1973_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1973_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_2002_, lean_object* v_msg_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Elab_Command_getRef___redArg(v___y_2004_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v_fileName_2009_; lean_object* v_fileMap_2010_; lean_object* v_currRecDepth_2011_; lean_object* v_cmdPos_2012_; lean_object* v_macroStack_2013_; lean_object* v_quotContext_x3f_2014_; lean_object* v_currMacroScope_2015_; lean_object* v_snap_x3f_2016_; lean_object* v_cancelTk_x3f_2017_; uint8_t v_suppressElabErrors_2018_; lean_object* v_ref_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v_fileName_2009_ = lean_ctor_get(v___y_2004_, 0);
v_fileMap_2010_ = lean_ctor_get(v___y_2004_, 1);
v_currRecDepth_2011_ = lean_ctor_get(v___y_2004_, 2);
v_cmdPos_2012_ = lean_ctor_get(v___y_2004_, 3);
v_macroStack_2013_ = lean_ctor_get(v___y_2004_, 4);
v_quotContext_x3f_2014_ = lean_ctor_get(v___y_2004_, 5);
v_currMacroScope_2015_ = lean_ctor_get(v___y_2004_, 6);
v_snap_x3f_2016_ = lean_ctor_get(v___y_2004_, 8);
v_cancelTk_x3f_2017_ = lean_ctor_get(v___y_2004_, 9);
v_suppressElabErrors_2018_ = lean_ctor_get_uint8(v___y_2004_, sizeof(void*)*10);
v_ref_2019_ = l_Lean_replaceRef(v_ref_2002_, v_a_2008_);
lean_dec(v_a_2008_);
lean_inc(v_cancelTk_x3f_2017_);
lean_inc(v_snap_x3f_2016_);
lean_inc(v_currMacroScope_2015_);
lean_inc(v_quotContext_x3f_2014_);
lean_inc(v_macroStack_2013_);
lean_inc(v_cmdPos_2012_);
lean_inc(v_currRecDepth_2011_);
lean_inc_ref(v_fileMap_2010_);
lean_inc_ref(v_fileName_2009_);
v___x_2020_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2020_, 0, v_fileName_2009_);
lean_ctor_set(v___x_2020_, 1, v_fileMap_2010_);
lean_ctor_set(v___x_2020_, 2, v_currRecDepth_2011_);
lean_ctor_set(v___x_2020_, 3, v_cmdPos_2012_);
lean_ctor_set(v___x_2020_, 4, v_macroStack_2013_);
lean_ctor_set(v___x_2020_, 5, v_quotContext_x3f_2014_);
lean_ctor_set(v___x_2020_, 6, v_currMacroScope_2015_);
lean_ctor_set(v___x_2020_, 7, v_ref_2019_);
lean_ctor_set(v___x_2020_, 8, v_snap_x3f_2016_);
lean_ctor_set(v___x_2020_, 9, v_cancelTk_x3f_2017_);
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*10, v_suppressElabErrors_2018_);
v___x_2021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_2003_, v___x_2020_, v___y_2005_);
lean_dec_ref(v___x_2020_);
return v___x_2021_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_msg_2003_);
v_a_2022_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2007_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2007_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2030_, lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2030_, v_msg_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v_ref_2030_);
return v_res_2035_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_val_2053_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = l_Lean_Syntax_getArg(v_stx_2042_, v___x_2060_);
switch(lean_obj_tag(v___x_2061_))
{
case 2:
{
lean_object* v_val_2062_; 
lean_dec(v_stx_2042_);
v_val_2062_ = lean_ctor_get(v___x_2061_, 1);
lean_inc_ref(v_val_2062_);
lean_dec_ref(v___x_2061_);
v_val_2053_ = v_val_2062_;
goto v___jp_2052_;
}
case 1:
{
lean_object* v_kind_2063_; 
v_kind_2063_ = lean_ctor_get(v___x_2061_, 1);
lean_inc(v_kind_2063_);
if (lean_obj_tag(v_kind_2063_) == 1)
{
lean_object* v_pre_2064_; 
v_pre_2064_ = lean_ctor_get(v_kind_2063_, 0);
lean_inc(v_pre_2064_);
if (lean_obj_tag(v_pre_2064_) == 1)
{
lean_object* v_pre_2065_; 
v_pre_2065_ = lean_ctor_get(v_pre_2064_, 0);
lean_inc(v_pre_2065_);
if (lean_obj_tag(v_pre_2065_) == 1)
{
lean_object* v_pre_2066_; 
v_pre_2066_ = lean_ctor_get(v_pre_2065_, 0);
lean_inc(v_pre_2066_);
if (lean_obj_tag(v_pre_2066_) == 1)
{
lean_object* v_pre_2067_; 
v_pre_2067_ = lean_ctor_get(v_pre_2066_, 0);
if (lean_obj_tag(v_pre_2067_) == 0)
{
lean_object* v_str_2068_; lean_object* v_str_2069_; lean_object* v_str_2070_; lean_object* v_str_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_str_2068_ = lean_ctor_get(v_kind_2063_, 1);
lean_inc_ref(v_str_2068_);
lean_dec_ref(v_kind_2063_);
v_str_2069_ = lean_ctor_get(v_pre_2064_, 1);
lean_inc_ref(v_str_2069_);
lean_dec_ref(v_pre_2064_);
v_str_2070_ = lean_ctor_get(v_pre_2065_, 1);
lean_inc_ref(v_str_2070_);
lean_dec_ref(v_pre_2065_);
v_str_2071_ = lean_ctor_get(v_pre_2066_, 1);
lean_inc_ref(v_str_2071_);
lean_dec_ref(v_pre_2066_);
v___x_2072_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0));
v___x_2073_ = lean_string_dec_eq(v_str_2071_, v___x_2072_);
lean_dec_ref(v_str_2071_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v_str_2070_);
lean_dec_ref(v_str_2069_);
lean_dec_ref(v_str_2068_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
else
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2075_ = lean_string_dec_eq(v_str_2070_, v___x_2074_);
lean_dec_ref(v_str_2070_);
if (v___x_2075_ == 0)
{
lean_dec_ref(v_str_2069_);
lean_dec_ref(v_str_2068_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2077_ = lean_string_dec_eq(v_str_2069_, v___x_2076_);
lean_dec_ref(v_str_2069_);
if (v___x_2077_ == 0)
{
lean_dec_ref(v_str_2068_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2079_ = lean_string_dec_eq(v_str_2068_, v___x_2078_);
lean_dec_ref(v_str_2068_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = l_Lean_Syntax_getArg(v___x_2061_, v___x_2080_);
lean_dec_ref(v___x_2061_);
if (lean_obj_tag(v___x_2081_) == 2)
{
lean_object* v_val_2082_; 
lean_dec(v_stx_2042_);
v_val_2082_ = lean_ctor_get(v___x_2081_, 1);
lean_inc_ref(v_val_2082_);
lean_dec_ref(v___x_2081_);
v_val_2053_ = v_val_2082_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v___x_2081_);
v___x_2083_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2042_);
v___x_2084_ = l_Lean_MessageData_ofSyntax(v_stx_2042_);
v___x_2085_ = l_Lean_indentD(v___x_2084_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2083_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2042_, v___x_2086_, v___y_2043_, v___y_2044_);
lean_dec(v_stx_2042_);
return v___x_2087_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2066_);
lean_dec_ref(v_pre_2065_);
lean_dec_ref(v_pre_2064_);
lean_dec_ref(v_kind_2063_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
}
else
{
lean_dec_ref(v_pre_2065_);
lean_dec(v_pre_2066_);
lean_dec_ref(v_pre_2064_);
lean_dec_ref(v_kind_2063_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
}
else
{
lean_dec_ref(v_pre_2064_);
lean_dec(v_pre_2065_);
lean_dec_ref(v_kind_2063_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
}
else
{
lean_dec(v_pre_2064_);
lean_dec_ref(v_kind_2063_);
lean_dec_ref(v___x_2061_);
goto v___jp_2046_;
}
}
else
{
lean_dec_ref(v___x_2061_);
lean_dec(v_kind_2063_);
goto v___jp_2046_;
}
}
default: 
{
lean_dec(v___x_2061_);
goto v___jp_2046_;
}
}
v___jp_2046_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2047_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2042_);
v___x_2048_ = l_Lean_MessageData_ofSyntax(v_stx_2042_);
v___x_2049_ = l_Lean_indentD(v___x_2048_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2047_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2042_, v___x_2050_, v___y_2043_, v___y_2044_);
lean_dec(v_stx_2042_);
return v___x_2051_;
}
v___jp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_string_utf8_byte_size(v_val_2053_);
v___x_2056_ = lean_unsigned_to_nat(2u);
v___x_2057_ = lean_nat_sub(v___x_2055_, v___x_2056_);
v___x_2058_ = lean_string_utf8_extract(v_val_2053_, v___x_2054_, v___x_2057_);
lean_dec(v___x_2057_);
lean_dec_ref(v_val_2053_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2093_, size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_b_2096_){
_start:
{
lean_object* v_a_2098_; uint8_t v___x_2102_; 
v___x_2102_ = lean_usize_dec_lt(v_i_2095_, v_sz_2094_);
if (v___x_2102_ == 0)
{
return v_b_2096_;
}
else
{
lean_object* v_a_2103_; lean_object* v_fst_2104_; lean_object* v_snd_2105_; lean_object* v_out_2106_; uint8_t v___x_2107_; 
v_a_2103_ = lean_array_uget_borrowed(v_as_2093_, v_i_2095_);
v_fst_2104_ = lean_ctor_get(v_a_2103_, 0);
v_snd_2105_ = lean_ctor_get(v_a_2103_, 1);
v_out_2106_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2107_ = lean_string_dec_eq(v_snd_2105_, v_out_2106_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2108_ = lean_unbox(v_fst_2104_);
v___x_2109_ = l_Lean_Diff_Action_linePrefix(v___x_2108_);
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2111_ = lean_string_append(v___x_2109_, v___x_2110_);
v___x_2112_ = lean_string_append(v___x_2111_, v_snd_2105_);
v___x_2113_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2114_ = lean_string_append(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_string_append(v_b_2096_, v___x_2114_);
lean_dec_ref(v___x_2114_);
v_a_2098_ = v___x_2115_;
goto v___jp_2097_;
}
else
{
uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2116_ = lean_unbox(v_fst_2104_);
v___x_2117_ = l_Lean_Diff_Action_linePrefix(v___x_2116_);
v___x_2118_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
v___x_2120_ = lean_string_append(v_b_2096_, v___x_2119_);
lean_dec_ref(v___x_2119_);
v_a_2098_ = v___x_2120_;
goto v___jp_2097_;
}
}
v___jp_2097_:
{
size_t v___x_2099_; size_t v___x_2100_; 
v___x_2099_ = ((size_t)1ULL);
v___x_2100_ = lean_usize_add(v_i_2095_, v___x_2099_);
v_i_2095_ = v___x_2100_;
v_b_2096_ = v_a_2098_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2121_, lean_object* v_sz_2122_, lean_object* v_i_2123_, lean_object* v_b_2124_){
_start:
{
size_t v_sz_boxed_2125_; size_t v_i_boxed_2126_; lean_object* v_res_2127_; 
v_sz_boxed_2125_ = lean_unbox_usize(v_sz_2122_);
lean_dec(v_sz_2122_);
v_i_boxed_2126_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2121_, v_sz_boxed_2125_, v_i_boxed_2126_, v_b_2124_);
lean_dec_ref(v_as_2121_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2128_){
_start:
{
lean_object* v_out_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v_out_2129_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2130_ = lean_array_size(v_lines_2128_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2128_, v_sz_2130_, v___x_2131_, v_out_2129_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2133_);
lean_dec_ref(v_lines_2133_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2135_, lean_object* v_as_x27_2136_, lean_object* v_b_2137_){
_start:
{
if (lean_obj_tag(v_as_x27_2136_) == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref(v_filterFn_2135_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_b_2137_);
return v___x_2139_;
}
else
{
lean_object* v_head_2140_; uint8_t v_isSilent_2141_; 
v_head_2140_ = lean_ctor_get(v_as_x27_2136_, 0);
v_isSilent_2141_ = lean_ctor_get_uint8(v_head_2140_, sizeof(void*)*5 + 2);
if (v_isSilent_2141_ == 0)
{
lean_object* v_tail_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2164_; 
v_tail_2142_ = lean_ctor_get(v_as_x27_2136_, 1);
v_fst_2143_ = lean_ctor_get(v_b_2137_, 0);
v_snd_2144_ = lean_ctor_get(v_b_2137_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_b_2137_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2146_ = v_b_2137_;
v_isShared_2147_ = v_isSharedCheck_2164_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_snd_2144_);
lean_inc(v_fst_2143_);
lean_dec(v_b_2137_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2164_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
lean_inc_ref(v_filterFn_2135_);
lean_inc(v_head_2140_);
v___x_2148_ = lean_apply_1(v_filterFn_2135_, v_head_2140_);
v___x_2149_ = lean_unbox(v___x_2148_);
switch(v___x_2149_)
{
case 0:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_inc(v_head_2140_);
v___x_2150_ = l_Lean_MessageLog_add(v_head_2140_, v_fst_2143_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2150_);
v___x_2152_ = v___x_2146_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2144_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v_as_x27_2136_ = v_tail_2142_;
v_b_2137_ = v___x_2152_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2156_; 
if (v_isShared_2147_ == 0)
{
v___x_2156_ = v___x_2146_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_fst_2143_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_snd_2144_);
v___x_2156_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
v_as_x27_2136_ = v_tail_2142_;
v_b_2137_ = v___x_2156_;
goto _start;
}
}
default: 
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_inc(v_head_2140_);
v___x_2159_ = l_Lean_MessageLog_add(v_head_2140_, v_snd_2144_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v___x_2159_);
v___x_2161_ = v___x_2146_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_fst_2143_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
v_as_x27_2136_ = v_tail_2142_;
v_b_2137_ = v___x_2161_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2165_; lean_object* v_fst_2166_; lean_object* v_snd_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2175_; 
v_tail_2165_ = lean_ctor_get(v_as_x27_2136_, 1);
v_fst_2166_ = lean_ctor_get(v_b_2137_, 0);
v_snd_2167_ = lean_ctor_get(v_b_2137_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_b_2137_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2169_ = v_b_2137_;
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_snd_2167_);
lean_inc(v_fst_2166_);
lean_dec(v_b_2137_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_fst_2166_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_snd_2167_);
v___x_2172_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_as_x27_2136_ = v_tail_2165_;
v_b_2137_ = v___x_2172_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2176_, lean_object* v_as_x27_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2176_, v_as_x27_2177_, v_b_2178_);
lean_dec(v_as_x27_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2181_, lean_object* v_a_2182_, uint8_t v_b_2183_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = 0;
switch(lean_obj_tag(v_a_2182_))
{
case 0:
{
uint8_t v___x_2185_; 
lean_dec_ref(v_a_2182_);
v___x_2185_ = 1;
return v___x_2185_;
}
case 1:
{
lean_object* v_pos_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2199_; 
v_pos_2186_ = lean_ctor_get(v_a_2182_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2182_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2188_ = v_a_2182_;
v_isShared_2189_ = v_isSharedCheck_2199_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_pos_2186_);
lean_dec(v_a_2182_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2199_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_str_2190_; lean_object* v_startInclusive_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v_str_2190_ = lean_ctor_get(v_s_2181_, 0);
v_startInclusive_2191_ = lean_ctor_get(v_s_2181_, 1);
v___x_2192_ = lean_nat_add(v_startInclusive_2191_, v_pos_2186_);
lean_dec(v_pos_2186_);
v___x_2193_ = lean_string_utf8_next_fast(v_str_2190_, v___x_2192_);
lean_dec(v___x_2192_);
v___x_2194_ = lean_nat_sub(v___x_2193_, v_startInclusive_2191_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2194_);
v___x_2196_ = v___x_2188_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_a_2182_ = v___x_2196_;
v_b_2183_ = v___x_2184_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2200_; lean_object* v_table_2201_; lean_object* v_stackPos_2202_; lean_object* v_needlePos_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2256_; 
v_needle_2200_ = lean_ctor_get(v_a_2182_, 0);
v_table_2201_ = lean_ctor_get(v_a_2182_, 1);
v_stackPos_2202_ = lean_ctor_get(v_a_2182_, 2);
v_needlePos_2203_ = lean_ctor_get(v_a_2182_, 3);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_a_2182_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2205_ = v_a_2182_;
v_isShared_2206_ = v_isSharedCheck_2256_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_needlePos_2203_);
lean_inc(v_stackPos_2202_);
lean_inc(v_table_2201_);
lean_inc(v_needle_2200_);
lean_dec(v_a_2182_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2256_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_str_2207_; lean_object* v_startInclusive_2208_; lean_object* v_endExclusive_2209_; lean_object* v_str_2210_; lean_object* v_startInclusive_2211_; lean_object* v_endExclusive_2212_; lean_object* v_basePos_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_str_2207_ = lean_ctor_get(v_needle_2200_, 0);
v_startInclusive_2208_ = lean_ctor_get(v_needle_2200_, 1);
v_endExclusive_2209_ = lean_ctor_get(v_needle_2200_, 2);
v_str_2210_ = lean_ctor_get(v_s_2181_, 0);
v_startInclusive_2211_ = lean_ctor_get(v_s_2181_, 1);
v_endExclusive_2212_ = lean_ctor_get(v_s_2181_, 2);
v_basePos_2213_ = lean_nat_sub(v_stackPos_2202_, v_needlePos_2203_);
v___x_2214_ = lean_nat_sub(v_endExclusive_2209_, v_startInclusive_2208_);
v___x_2215_ = lean_nat_add(v_basePos_2213_, v___x_2214_);
v___x_2216_ = lean_nat_sub(v_endExclusive_2212_, v_startInclusive_2211_);
v___x_2217_ = lean_nat_dec_le(v___x_2215_, v___x_2216_);
lean_dec(v___x_2215_);
if (v___x_2217_ == 0)
{
uint8_t v___x_2218_; 
lean_dec(v___x_2214_);
lean_del_object(v___x_2205_);
lean_dec(v_needlePos_2203_);
lean_dec(v_stackPos_2202_);
lean_dec_ref(v_table_2201_);
lean_dec_ref(v_needle_2200_);
v___x_2218_ = lean_nat_dec_lt(v_basePos_2213_, v___x_2216_);
lean_dec(v___x_2216_);
lean_dec(v_basePos_2213_);
if (v___x_2218_ == 0)
{
return v_b_2183_;
}
else
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_box(3);
v_a_2182_ = v___x_2219_;
v_b_2183_ = v___x_2184_;
goto _start;
}
}
else
{
lean_object* v___x_2221_; uint8_t v_stackByte_2222_; lean_object* v___x_2223_; uint8_t v_patByte_2224_; uint8_t v___x_2225_; 
lean_dec(v___x_2216_);
lean_dec(v_basePos_2213_);
v___x_2221_ = lean_nat_add(v_startInclusive_2211_, v_stackPos_2202_);
v_stackByte_2222_ = lean_string_get_byte_fast(v_str_2210_, v___x_2221_);
v___x_2223_ = lean_nat_add(v_startInclusive_2208_, v_needlePos_2203_);
v_patByte_2224_ = lean_string_get_byte_fast(v_str_2207_, v___x_2223_);
v___x_2225_ = lean_uint8_dec_eq(v_stackByte_2222_, v_patByte_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
lean_dec(v___x_2214_);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_nat_dec_eq(v_needlePos_2203_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v_newNeedlePos_2230_; uint8_t v___x_2231_; 
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_sub(v_needlePos_2203_, v___x_2228_);
lean_dec(v_needlePos_2203_);
v_newNeedlePos_2230_ = lean_array_fget_borrowed(v_table_2201_, v___x_2229_);
lean_dec(v___x_2229_);
v___x_2231_ = lean_nat_dec_eq(v_newNeedlePos_2230_, v___x_2226_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2233_; 
lean_inc(v_newNeedlePos_2230_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 3, v_newNeedlePos_2230_);
v___x_2233_ = v___x_2205_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_needle_2200_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_table_2201_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_stackPos_2202_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_newNeedlePos_2230_);
v___x_2233_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
v_a_2182_ = v___x_2233_;
v_b_2183_ = v___x_2184_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2236_; lean_object* v___x_2238_; 
v_nextStackPos_2236_ = l_String_Slice_posGE___redArg(v_s_2181_, v_stackPos_2202_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 3, v___x_2226_);
lean_ctor_set(v___x_2205_, 2, v_nextStackPos_2236_);
v___x_2238_ = v___x_2205_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_needle_2200_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_table_2201_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_nextStackPos_2236_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v___x_2226_);
v___x_2238_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
v_a_2182_ = v___x_2238_;
v_b_2183_ = v___x_2184_;
goto _start;
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_nextStackPos_2243_; lean_object* v___x_2245_; 
lean_dec(v_needlePos_2203_);
v___x_2241_ = lean_unsigned_to_nat(1u);
v___x_2242_ = lean_nat_add(v_stackPos_2202_, v___x_2241_);
lean_dec(v_stackPos_2202_);
v_nextStackPos_2243_ = l_String_Slice_posGE___redArg(v_s_2181_, v___x_2242_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 3, v___x_2226_);
lean_ctor_set(v___x_2205_, 2, v_nextStackPos_2243_);
v___x_2245_ = v___x_2205_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_needle_2200_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_table_2201_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_nextStackPos_2243_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v___x_2226_);
v___x_2245_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v_a_2182_ = v___x_2245_;
v_b_2183_ = v___x_2184_;
goto _start;
}
}
}
else
{
lean_object* v___x_2248_; lean_object* v_nextNeedlePos_2249_; uint8_t v___x_2250_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2249_ = lean_nat_add(v_needlePos_2203_, v___x_2248_);
lean_dec(v_needlePos_2203_);
v___x_2250_ = lean_nat_dec_eq(v_nextNeedlePos_2249_, v___x_2214_);
lean_dec(v___x_2214_);
if (v___x_2250_ == 0)
{
lean_object* v_nextStackPos_2251_; lean_object* v___x_2253_; 
v_nextStackPos_2251_ = lean_nat_add(v_stackPos_2202_, v___x_2248_);
lean_dec(v_stackPos_2202_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 3, v_nextNeedlePos_2249_);
lean_ctor_set(v___x_2205_, 2, v_nextStackPos_2251_);
v___x_2253_ = v___x_2205_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_needle_2200_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_table_2201_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_nextStackPos_2251_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_nextNeedlePos_2249_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
v_a_2182_ = v___x_2253_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2249_);
lean_del_object(v___x_2205_);
lean_dec(v_stackPos_2202_);
lean_dec_ref(v_table_2201_);
lean_dec_ref(v_needle_2200_);
return v___x_2250_;
}
}
}
}
}
default: 
{
return v_b_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2257_, lean_object* v_a_2258_, lean_object* v_b_2259_){
_start:
{
uint8_t v_b_boxed_2260_; uint8_t v_res_2261_; lean_object* v_r_2262_; 
v_b_boxed_2260_ = lean_unbox(v_b_2259_);
v_res_2261_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2257_, v_a_2258_, v_b_boxed_2260_);
lean_dec_ref(v_s_2257_);
v_r_2262_ = lean_box(v_res_2261_);
return v_r_2262_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2263_, lean_object* v_s_2264_){
_start:
{
lean_object* v___y_2266_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_string_utf8_byte_size(v___x_2263_);
v___x_2271_ = lean_nat_dec_eq(v___x_2270_, v___x_2269_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2263_);
lean_ctor_set(v___x_2272_, 1, v___x_2269_);
lean_ctor_set(v___x_2272_, 2, v___x_2270_);
v___x_2273_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2272_);
v___x_2274_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
lean_ctor_set(v___x_2274_, 2, v___x_2269_);
lean_ctor_set(v___x_2274_, 3, v___x_2269_);
v___y_2266_ = v___x_2274_;
goto v___jp_2265_;
}
else
{
lean_object* v___x_2275_; 
lean_dec_ref(v___x_2263_);
v___x_2275_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2266_ = v___x_2275_;
goto v___jp_2265_;
}
v___jp_2265_:
{
uint8_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = 0;
v___x_2268_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2264_, v___y_2266_, v___x_2267_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2276_, lean_object* v_s_2277_){
_start:
{
uint8_t v_res_2278_; lean_object* v_r_2279_; 
v_res_2278_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2276_, v_s_2277_);
lean_dec_ref(v_s_2277_);
v_r_2279_ = lean_box(v_res_2278_);
return v_r_2279_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2280_, uint8_t v_suppressElabErrors_2281_, lean_object* v_x_2282_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 1)
{
lean_object* v_pre_2283_; 
v_pre_2283_ = lean_ctor_get(v_x_2282_, 0);
if (lean_obj_tag(v_pre_2283_) == 0)
{
lean_object* v_str_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_str_2284_ = lean_ctor_get(v_x_2282_, 1);
v___x_2285_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2286_ = lean_string_dec_eq(v_str_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
return v___y_2280_;
}
else
{
return v_suppressElabErrors_2281_;
}
}
else
{
return v___y_2280_;
}
}
else
{
return v___y_2280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2287_, lean_object* v_suppressElabErrors_2288_, lean_object* v_x_2289_){
_start:
{
uint8_t v___y_29320__boxed_2290_; uint8_t v_suppressElabErrors_boxed_2291_; uint8_t v_res_2292_; lean_object* v_r_2293_; 
v___y_29320__boxed_2290_ = lean_unbox(v___y_2287_);
v_suppressElabErrors_boxed_2291_ = lean_unbox(v_suppressElabErrors_2288_);
v_res_2292_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29320__boxed_2290_, v_suppressElabErrors_boxed_2291_, v_x_2289_);
lean_dec(v_x_2289_);
v_r_2293_ = lean_box(v_res_2292_);
return v_r_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2294_, lean_object* v_msgData_2295_, uint8_t v_severity_2296_, uint8_t v_isSilent_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; uint8_t v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; uint8_t v___y_2365_; uint8_t v___y_2366_; uint8_t v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; uint8_t v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2401_; uint8_t v___y_2402_; uint8_t v___y_2403_; uint8_t v___x_2418_; uint8_t v___y_2420_; uint8_t v___y_2421_; uint8_t v___y_2422_; uint8_t v___y_2424_; uint8_t v___x_2436_; 
v___x_2418_ = 2;
v___x_2436_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2296_, v___x_2418_);
if (v___x_2436_ == 0)
{
v___y_2424_ = v___x_2436_;
goto v___jp_2423_;
}
else
{
uint8_t v___x_2437_; 
lean_inc_ref(v_msgData_2295_);
v___x_2437_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2295_);
v___y_2424_ = v___x_2437_;
goto v___jp_2423_;
}
v___jp_2301_:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Elab_Command_getScope___redArg(v___y_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l_Lean_Elab_Command_getScope___redArg(v___y_2309_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2347_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2347_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2347_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v_currNamespace_2318_; lean_object* v_openDecls_2319_; lean_object* v_env_2320_; lean_object* v_messages_2321_; lean_object* v_scopes_2322_; lean_object* v_usedQuotCtxts_2323_; lean_object* v_nextMacroScope_2324_; lean_object* v_maxRecDepth_2325_; lean_object* v_ngen_2326_; lean_object* v_auxDeclNGen_2327_; lean_object* v_infoState_2328_; lean_object* v_traceState_2329_; lean_object* v_snapshotTasks_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2346_; 
v___x_2317_ = lean_st_ref_take(v___y_2309_);
v_currNamespace_2318_ = lean_ctor_get(v_a_2311_, 2);
lean_inc(v_currNamespace_2318_);
lean_dec(v_a_2311_);
v_openDecls_2319_ = lean_ctor_get(v_a_2313_, 3);
lean_inc(v_openDecls_2319_);
lean_dec(v_a_2313_);
v_env_2320_ = lean_ctor_get(v___x_2317_, 0);
v_messages_2321_ = lean_ctor_get(v___x_2317_, 1);
v_scopes_2322_ = lean_ctor_get(v___x_2317_, 2);
v_usedQuotCtxts_2323_ = lean_ctor_get(v___x_2317_, 3);
v_nextMacroScope_2324_ = lean_ctor_get(v___x_2317_, 4);
v_maxRecDepth_2325_ = lean_ctor_get(v___x_2317_, 5);
v_ngen_2326_ = lean_ctor_get(v___x_2317_, 6);
v_auxDeclNGen_2327_ = lean_ctor_get(v___x_2317_, 7);
v_infoState_2328_ = lean_ctor_get(v___x_2317_, 8);
v_traceState_2329_ = lean_ctor_get(v___x_2317_, 9);
v_snapshotTasks_2330_ = lean_ctor_get(v___x_2317_, 10);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2332_ = v___x_2317_;
v_isShared_2333_ = v_isSharedCheck_2346_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_snapshotTasks_2330_);
lean_inc(v_traceState_2329_);
lean_inc(v_infoState_2328_);
lean_inc(v_auxDeclNGen_2327_);
lean_inc(v_ngen_2326_);
lean_inc(v_maxRecDepth_2325_);
lean_inc(v_nextMacroScope_2324_);
lean_inc(v_usedQuotCtxts_2323_);
lean_inc(v_scopes_2322_);
lean_inc(v_messages_2321_);
lean_inc(v_env_2320_);
lean_dec(v___x_2317_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2346_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_currNamespace_2318_);
lean_ctor_set(v___x_2334_, 1, v_openDecls_2319_);
v___x_2335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___y_2308_);
lean_inc_ref(v___y_2303_);
lean_inc_ref(v___y_2307_);
v___x_2336_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2336_, 0, v___y_2307_);
lean_ctor_set(v___x_2336_, 1, v___y_2305_);
lean_ctor_set(v___x_2336_, 2, v___y_2304_);
lean_ctor_set(v___x_2336_, 3, v___y_2303_);
lean_ctor_set(v___x_2336_, 4, v___x_2335_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*5, v___y_2306_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*5 + 1, v___y_2302_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*5 + 2, v_isSilent_2297_);
v___x_2337_ = l_Lean_MessageLog_add(v___x_2336_, v_messages_2321_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 1, v___x_2337_);
v___x_2339_ = v___x_2332_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_env_2320_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_scopes_2322_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_usedQuotCtxts_2323_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_nextMacroScope_2324_);
lean_ctor_set(v_reuseFailAlloc_2345_, 5, v_maxRecDepth_2325_);
lean_ctor_set(v_reuseFailAlloc_2345_, 6, v_ngen_2326_);
lean_ctor_set(v_reuseFailAlloc_2345_, 7, v_auxDeclNGen_2327_);
lean_ctor_set(v_reuseFailAlloc_2345_, 8, v_infoState_2328_);
lean_ctor_set(v_reuseFailAlloc_2345_, 9, v_traceState_2329_);
lean_ctor_set(v_reuseFailAlloc_2345_, 10, v_snapshotTasks_2330_);
v___x_2339_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2340_ = lean_st_ref_set(v___y_2309_, v___x_2339_);
v___x_2341_ = lean_box(0);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2341_);
v___x_2343_ = v___x_2315_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
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
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_a_2311_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
v_a_2348_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2312_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2312_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___y_2308_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
v_a_2356_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2310_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2310_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
v___jp_2364_:
{
lean_object* v_fileName_2370_; lean_object* v_fileMap_2371_; uint8_t v_suppressElabErrors_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2391_; 
v_fileName_2370_ = lean_ctor_get(v___y_2298_, 0);
v_fileMap_2371_ = lean_ctor_get(v___y_2298_, 1);
v_suppressElabErrors_2372_ = lean_ctor_get_uint8(v___y_2298_, sizeof(void*)*10);
v___x_2373_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2295_);
v___x_2374_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2373_, v___y_2299_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2391_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2391_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_inc_ref_n(v_fileMap_2371_, 2);
v___x_2379_ = l_Lean_FileMap_toPosition(v_fileMap_2371_, v___y_2368_);
lean_dec(v___y_2368_);
v___x_2380_ = l_Lean_FileMap_toPosition(v_fileMap_2371_, v___y_2369_);
lean_dec(v___y_2369_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2372_ == 0)
{
lean_del_object(v___x_2377_);
v___y_2302_ = v___y_2366_;
v___y_2303_ = v___x_2382_;
v___y_2304_ = v___x_2381_;
v___y_2305_ = v___x_2379_;
v___y_2306_ = v___y_2367_;
v___y_2307_ = v_fileName_2370_;
v___y_2308_ = v_a_2375_;
v___y_2309_ = v___y_2299_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; uint8_t v___x_2386_; 
v___x_2383_ = lean_box(v___y_2365_);
v___x_2384_ = lean_box(v_suppressElabErrors_2372_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2385_, 0, v___x_2383_);
lean_closure_set(v___f_2385_, 1, v___x_2384_);
lean_inc(v_a_2375_);
v___x_2386_ = l_Lean_MessageData_hasTag(v___f_2385_, v_a_2375_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_dec_ref(v___x_2381_);
lean_dec_ref(v___x_2379_);
lean_dec(v_a_2375_);
v___x_2387_ = lean_box(0);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2387_);
v___x_2389_ = v___x_2377_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
else
{
lean_del_object(v___x_2377_);
v___y_2302_ = v___y_2366_;
v___y_2303_ = v___x_2382_;
v___y_2304_ = v___x_2381_;
v___y_2305_ = v___x_2379_;
v___y_2306_ = v___y_2367_;
v___y_2307_ = v_fileName_2370_;
v___y_2308_ = v_a_2375_;
v___y_2309_ = v___y_2299_;
goto v___jp_2301_;
}
}
}
}
v___jp_2392_:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Syntax_getTailPos_x3f(v___y_2395_, v___y_2396_);
lean_dec(v___y_2395_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_inc(v___y_2397_);
v___y_2365_ = v___y_2393_;
v___y_2366_ = v___y_2394_;
v___y_2367_ = v___y_2396_;
v___y_2368_ = v___y_2397_;
v___y_2369_ = v___y_2397_;
goto v___jp_2364_;
}
else
{
lean_object* v_val_2399_; 
v_val_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_val_2399_);
lean_dec_ref(v___x_2398_);
v___y_2365_ = v___y_2393_;
v___y_2366_ = v___y_2394_;
v___y_2367_ = v___y_2396_;
v___y_2368_ = v___y_2397_;
v___y_2369_ = v_val_2399_;
goto v___jp_2364_;
}
}
v___jp_2400_:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_Elab_Command_getRef___redArg(v___y_2298_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v_ref_2406_; lean_object* v___x_2407_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2404_);
v_ref_2406_ = l_Lean_replaceRef(v_ref_2294_, v_a_2405_);
lean_dec(v_a_2405_);
v___x_2407_ = l_Lean_Syntax_getPos_x3f(v_ref_2406_, v___y_2402_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_unsigned_to_nat(0u);
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2403_;
v___y_2395_ = v_ref_2406_;
v___y_2396_ = v___y_2402_;
v___y_2397_ = v___x_2408_;
goto v___jp_2392_;
}
else
{
lean_object* v_val_2409_; 
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_val_2409_);
lean_dec_ref(v___x_2407_);
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2403_;
v___y_2395_ = v_ref_2406_;
v___y_2396_ = v___y_2402_;
v___y_2397_ = v_val_2409_;
goto v___jp_2392_;
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v_msgData_2295_);
v_a_2410_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2404_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2404_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
v___jp_2419_:
{
if (v___y_2422_ == 0)
{
v___y_2401_ = v___y_2420_;
v___y_2402_ = v___y_2421_;
v___y_2403_ = v_severity_2296_;
goto v___jp_2400_;
}
else
{
v___y_2401_ = v___y_2420_;
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___x_2418_;
goto v___jp_2400_;
}
}
v___jp_2423_:
{
if (v___y_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v_scopes_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_opts_2429_; uint8_t v___x_2430_; uint8_t v___x_2431_; 
v___x_2425_ = lean_st_ref_get(v___y_2299_);
v_scopes_2426_ = lean_ctor_get(v___x_2425_, 2);
lean_inc(v_scopes_2426_);
lean_dec(v___x_2425_);
v___x_2427_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2428_ = l_List_head_x21___redArg(v___x_2427_, v_scopes_2426_);
lean_dec(v_scopes_2426_);
v_opts_2429_ = lean_ctor_get(v___x_2428_, 1);
lean_inc_ref(v_opts_2429_);
lean_dec(v___x_2428_);
v___x_2430_ = 1;
v___x_2431_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2296_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_dec_ref(v_opts_2429_);
v___y_2420_ = v___y_2424_;
v___y_2421_ = v___y_2424_;
v___y_2422_ = v___x_2431_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = l_Lean_warningAsError;
v___x_2433_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2429_, v___x_2432_);
lean_dec_ref(v_opts_2429_);
v___y_2420_ = v___y_2424_;
v___y_2421_ = v___y_2424_;
v___y_2422_ = v___x_2433_;
goto v___jp_2419_;
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v_msgData_2295_);
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2438_, lean_object* v_msgData_2439_, lean_object* v_severity_2440_, lean_object* v_isSilent_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v_severity_boxed_2445_; uint8_t v_isSilent_boxed_2446_; lean_object* v_res_2447_; 
v_severity_boxed_2445_ = lean_unbox(v_severity_2440_);
v_isSilent_boxed_2446_ = lean_unbox(v_isSilent_2441_);
v_res_2447_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2438_, v_msgData_2439_, v_severity_boxed_2445_, v_isSilent_boxed_2446_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v_ref_2438_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2448_, lean_object* v_msgData_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = 2;
v___x_2454_ = 0;
v___x_2455_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2448_, v_msgData_2449_, v___x_2453_, v___x_2454_, v___y_2450_, v___y_2451_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2456_, lean_object* v_msgData_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2456_, v_msgData_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v_ref_2456_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2462_, lean_object* v___x_2463_, lean_object* v___x_2464_, lean_object* v_a_2465_, lean_object* v_b_2466_){
_start:
{
lean_object* v_it_2468_; lean_object* v_startInclusive_2469_; lean_object* v_endExclusive_2470_; 
if (lean_obj_tag(v_a_2465_) == 0)
{
lean_object* v_currPos_2475_; lean_object* v_searcher_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2505_; 
v_currPos_2475_ = lean_ctor_get(v_a_2465_, 0);
v_searcher_2476_ = lean_ctor_get(v_a_2465_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2465_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2478_ = v_a_2465_;
v_isShared_2479_ = v_isSharedCheck_2505_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_searcher_2476_);
lean_inc(v_currPos_2475_);
lean_dec(v_a_2465_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2505_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_str_2480_; lean_object* v_startInclusive_2481_; lean_object* v_endExclusive_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v_str_2480_ = lean_ctor_get(v___x_2463_, 0);
v_startInclusive_2481_ = lean_ctor_get(v___x_2463_, 1);
v_endExclusive_2482_ = lean_ctor_get(v___x_2463_, 2);
v___x_2483_ = lean_nat_sub(v_endExclusive_2482_, v_startInclusive_2481_);
v___x_2484_ = lean_nat_dec_eq(v_searcher_2476_, v___x_2483_);
lean_dec(v___x_2483_);
if (v___x_2484_ == 0)
{
uint32_t v___x_2485_; lean_object* v___x_2486_; uint32_t v___x_2487_; uint8_t v___x_2488_; 
v___x_2485_ = 10;
v___x_2486_ = lean_nat_add(v_startInclusive_2481_, v_searcher_2476_);
v___x_2487_ = lean_string_utf8_get_fast(v_str_2480_, v___x_2486_);
v___x_2488_ = lean_uint32_dec_eq(v___x_2487_, v___x_2485_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_dec(v_searcher_2476_);
v___x_2489_ = lean_string_utf8_next_fast(v_str_2480_, v___x_2486_);
lean_dec(v___x_2486_);
v___x_2490_ = lean_nat_sub(v___x_2489_, v_startInclusive_2481_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2490_);
v___x_2492_ = v___x_2478_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_currPos_2475_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
v_a_2465_ = v___x_2492_;
goto _start;
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_slice_2498_; lean_object* v_nextIt_2500_; 
v___x_2495_ = lean_string_utf8_next_fast(v_str_2480_, v___x_2486_);
v___x_2496_ = lean_nat_sub(v___x_2495_, v___x_2486_);
lean_dec(v___x_2486_);
v___x_2497_ = lean_nat_add(v_searcher_2476_, v___x_2496_);
lean_dec(v___x_2496_);
v_slice_2498_ = l_String_Slice_subslice_x21(v___x_2463_, v_currPos_2475_, v_searcher_2476_);
lean_inc(v___x_2497_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2497_);
lean_ctor_set(v___x_2478_, 0, v___x_2497_);
v_nextIt_2500_ = v___x_2478_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2497_);
v_nextIt_2500_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v_startInclusive_2501_; lean_object* v_endExclusive_2502_; 
v_startInclusive_2501_ = lean_ctor_get(v_slice_2498_, 0);
lean_inc(v_startInclusive_2501_);
v_endExclusive_2502_ = lean_ctor_get(v_slice_2498_, 1);
lean_inc(v_endExclusive_2502_);
lean_dec_ref(v_slice_2498_);
v_it_2468_ = v_nextIt_2500_;
v_startInclusive_2469_ = v_startInclusive_2501_;
v_endExclusive_2470_ = v_endExclusive_2502_;
goto v___jp_2467_;
}
}
}
else
{
lean_object* v___x_2504_; 
lean_del_object(v___x_2478_);
lean_dec(v_searcher_2476_);
v___x_2504_ = lean_box(1);
lean_inc(v___x_2464_);
v_it_2468_ = v___x_2504_;
v_startInclusive_2469_ = v_currPos_2475_;
v_endExclusive_2470_ = v___x_2464_;
goto v___jp_2467_;
}
}
}
else
{
lean_dec(v___x_2464_);
lean_dec_ref(v___x_2462_);
return v_b_2466_;
}
v___jp_2467_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_inc_ref(v___x_2462_);
v___x_2471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2462_);
lean_ctor_set(v___x_2471_, 1, v_startInclusive_2469_);
lean_ctor_set(v___x_2471_, 2, v_endExclusive_2470_);
v___x_2472_ = l_String_Slice_toString(v___x_2471_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = lean_array_push(v_b_2466_, v___x_2472_);
v_a_2465_ = v_it_2468_;
v_b_2466_ = v___x_2473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2506_, lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2506_, v___x_2507_, v___x_2508_, v_a_2509_, v_b_2510_);
lean_dec_ref(v___x_2507_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2512_, lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v_a_2515_, lean_object* v_b_2516_){
_start:
{
lean_object* v_it_2518_; lean_object* v_startInclusive_2519_; lean_object* v_endExclusive_2520_; 
if (lean_obj_tag(v_a_2515_) == 0)
{
lean_object* v_currPos_2525_; lean_object* v_searcher_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2555_; 
v_currPos_2525_ = lean_ctor_get(v_a_2515_, 0);
v_searcher_2526_ = lean_ctor_get(v_a_2515_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_a_2515_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2528_ = v_a_2515_;
v_isShared_2529_ = v_isSharedCheck_2555_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_searcher_2526_);
lean_inc(v_currPos_2525_);
lean_dec(v_a_2515_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2555_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_str_2530_; lean_object* v_startInclusive_2531_; lean_object* v_endExclusive_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_str_2530_ = lean_ctor_get(v___x_2513_, 0);
v_startInclusive_2531_ = lean_ctor_get(v___x_2513_, 1);
v_endExclusive_2532_ = lean_ctor_get(v___x_2513_, 2);
v___x_2533_ = lean_nat_sub(v_endExclusive_2532_, v_startInclusive_2531_);
v___x_2534_ = lean_nat_dec_eq(v_searcher_2526_, v___x_2533_);
lean_dec(v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; uint32_t v___x_2536_; uint32_t v___x_2537_; uint8_t v___x_2538_; 
v___x_2535_ = lean_nat_add(v_startInclusive_2531_, v_searcher_2526_);
v___x_2536_ = lean_string_utf8_get_fast(v_str_2530_, v___x_2535_);
v___x_2537_ = 10;
v___x_2538_ = lean_uint32_dec_eq(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_dec(v_searcher_2526_);
v___x_2539_ = lean_string_utf8_next_fast(v_str_2530_, v___x_2535_);
lean_dec(v___x_2535_);
v___x_2540_ = lean_nat_sub(v___x_2539_, v_startInclusive_2531_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2540_);
v___x_2542_ = v___x_2528_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_currPos_2525_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; 
v___x_2543_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2512_, v___x_2513_, v___x_2514_, v___x_2542_, v_b_2516_);
return v___x_2543_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_slice_2548_; lean_object* v_nextIt_2550_; 
v___x_2545_ = lean_string_utf8_next_fast(v_str_2530_, v___x_2535_);
v___x_2546_ = lean_nat_sub(v___x_2545_, v___x_2535_);
lean_dec(v___x_2535_);
v___x_2547_ = lean_nat_add(v_searcher_2526_, v___x_2546_);
lean_dec(v___x_2546_);
v_slice_2548_ = l_String_Slice_subslice_x21(v___x_2513_, v_currPos_2525_, v_searcher_2526_);
lean_inc(v___x_2547_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2547_);
lean_ctor_set(v___x_2528_, 0, v___x_2547_);
v_nextIt_2550_ = v___x_2528_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2547_);
v_nextIt_2550_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v_startInclusive_2551_; lean_object* v_endExclusive_2552_; 
v_startInclusive_2551_ = lean_ctor_get(v_slice_2548_, 0);
lean_inc(v_startInclusive_2551_);
v_endExclusive_2552_ = lean_ctor_get(v_slice_2548_, 1);
lean_inc(v_endExclusive_2552_);
lean_dec_ref(v_slice_2548_);
v_it_2518_ = v_nextIt_2550_;
v_startInclusive_2519_ = v_startInclusive_2551_;
v_endExclusive_2520_ = v_endExclusive_2552_;
goto v___jp_2517_;
}
}
}
else
{
lean_object* v___x_2554_; 
lean_del_object(v___x_2528_);
lean_dec(v_searcher_2526_);
v___x_2554_ = lean_box(1);
lean_inc(v___x_2514_);
v_it_2518_ = v___x_2554_;
v_startInclusive_2519_ = v_currPos_2525_;
v_endExclusive_2520_ = v___x_2514_;
goto v___jp_2517_;
}
}
}
else
{
lean_dec(v___x_2514_);
lean_dec_ref(v___x_2512_);
return v_b_2516_;
}
v___jp_2517_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_inc_ref(v___x_2512_);
v___x_2521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2512_);
lean_ctor_set(v___x_2521_, 1, v_startInclusive_2519_);
lean_ctor_set(v___x_2521_, 2, v_endExclusive_2520_);
v___x_2522_ = l_String_Slice_toString(v___x_2521_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = lean_array_push(v_b_2516_, v___x_2522_);
v___x_2524_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2512_, v___x_2513_, v___x_2514_, v_it_2518_, v___x_2523_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2556_, lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v_a_2559_, lean_object* v_b_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2556_, v___x_2557_, v___x_2558_, v_a_2559_, v_b_2560_);
lean_dec_ref(v___x_2557_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; lean_object* v_infoState_2566_; uint8_t v_enabled_2567_; 
v___x_2565_ = lean_st_ref_get(v___y_2563_);
v_infoState_2566_ = lean_ctor_get(v___x_2565_, 8);
lean_inc_ref(v_infoState_2566_);
lean_dec(v___x_2565_);
v_enabled_2567_ = lean_ctor_get_uint8(v_infoState_2566_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2566_);
if (v_enabled_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec_ref(v_t_2562_);
v___x_2568_ = lean_box(0);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
return v___x_2569_;
}
else
{
lean_object* v___x_2570_; lean_object* v_infoState_2571_; lean_object* v_env_2572_; lean_object* v_messages_2573_; lean_object* v_scopes_2574_; lean_object* v_usedQuotCtxts_2575_; lean_object* v_nextMacroScope_2576_; lean_object* v_maxRecDepth_2577_; lean_object* v_ngen_2578_; lean_object* v_auxDeclNGen_2579_; lean_object* v_traceState_2580_; lean_object* v_snapshotTasks_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2603_; 
v___x_2570_ = lean_st_ref_take(v___y_2563_);
v_infoState_2571_ = lean_ctor_get(v___x_2570_, 8);
v_env_2572_ = lean_ctor_get(v___x_2570_, 0);
v_messages_2573_ = lean_ctor_get(v___x_2570_, 1);
v_scopes_2574_ = lean_ctor_get(v___x_2570_, 2);
v_usedQuotCtxts_2575_ = lean_ctor_get(v___x_2570_, 3);
v_nextMacroScope_2576_ = lean_ctor_get(v___x_2570_, 4);
v_maxRecDepth_2577_ = lean_ctor_get(v___x_2570_, 5);
v_ngen_2578_ = lean_ctor_get(v___x_2570_, 6);
v_auxDeclNGen_2579_ = lean_ctor_get(v___x_2570_, 7);
v_traceState_2580_ = lean_ctor_get(v___x_2570_, 9);
v_snapshotTasks_2581_ = lean_ctor_get(v___x_2570_, 10);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2583_ = v___x_2570_;
v_isShared_2584_ = v_isSharedCheck_2603_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_snapshotTasks_2581_);
lean_inc(v_traceState_2580_);
lean_inc(v_infoState_2571_);
lean_inc(v_auxDeclNGen_2579_);
lean_inc(v_ngen_2578_);
lean_inc(v_maxRecDepth_2577_);
lean_inc(v_nextMacroScope_2576_);
lean_inc(v_usedQuotCtxts_2575_);
lean_inc(v_scopes_2574_);
lean_inc(v_messages_2573_);
lean_inc(v_env_2572_);
lean_dec(v___x_2570_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2603_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint8_t v_enabled_2585_; lean_object* v_assignment_2586_; lean_object* v_lazyAssignment_2587_; lean_object* v_trees_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2602_; 
v_enabled_2585_ = lean_ctor_get_uint8(v_infoState_2571_, sizeof(void*)*3);
v_assignment_2586_ = lean_ctor_get(v_infoState_2571_, 0);
v_lazyAssignment_2587_ = lean_ctor_get(v_infoState_2571_, 1);
v_trees_2588_ = lean_ctor_get(v_infoState_2571_, 2);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_infoState_2571_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2590_ = v_infoState_2571_;
v_isShared_2591_ = v_isSharedCheck_2602_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_trees_2588_);
lean_inc(v_lazyAssignment_2587_);
lean_inc(v_assignment_2586_);
lean_dec(v_infoState_2571_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2602_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = l_Lean_PersistentArray_push___redArg(v_trees_2588_, v_t_2562_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 2, v___x_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_assignment_2586_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_lazyAssignment_2587_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v___x_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*3, v_enabled_2585_);
v___x_2594_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 8, v___x_2594_);
v___x_2596_ = v___x_2583_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_env_2572_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_messages_2573_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_scopes_2574_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_usedQuotCtxts_2575_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_nextMacroScope_2576_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_maxRecDepth_2577_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_ngen_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 7, v_auxDeclNGen_2579_);
lean_ctor_set(v_reuseFailAlloc_2600_, 8, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2600_, 9, v_traceState_2580_);
lean_ctor_set(v_reuseFailAlloc_2600_, 10, v_snapshotTasks_2581_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_st_ref_set(v___y_2563_, v___x_2596_);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2604_, v___y_2605_);
lean_dec(v___y_2605_);
return v_res_2607_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_unsigned_to_nat(32u);
v___x_2609_ = lean_mk_empty_array_with_capacity(v___x_2608_);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2611_ = ((size_t)5ULL);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_unsigned_to_nat(32u);
v___x_2614_ = lean_mk_empty_array_with_capacity(v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2616_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2614_);
lean_ctor_set(v___x_2616_, 2, v___x_2612_);
lean_ctor_set(v___x_2616_, 3, v___x_2612_);
lean_ctor_set_usize(v___x_2616_, 4, v___x_2611_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; lean_object* v_infoState_2622_; uint8_t v_enabled_2623_; 
v___x_2621_ = lean_st_ref_get(v___y_2619_);
v_infoState_2622_ = lean_ctor_get(v___x_2621_, 8);
lean_inc_ref(v_infoState_2622_);
lean_dec(v___x_2621_);
v_enabled_2623_ = lean_ctor_get_uint8(v_infoState_2622_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2622_);
if (v_enabled_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v_t_2617_);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
return v___x_2625_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_t_2617_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2627_, v___y_2619_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_2634_, lean_object* v_edited_2635_, lean_object* v_b_2636_){
_start:
{
lean_object* v_fst_2637_; lean_object* v_snd_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2657_; 
v_fst_2637_ = lean_ctor_get(v_b_2636_, 0);
v_snd_2638_ = lean_ctor_get(v_b_2636_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_b_2636_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2640_ = v_b_2636_;
v_isShared_2641_ = v_isSharedCheck_2657_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_snd_2638_);
lean_inc(v_fst_2637_);
lean_dec(v_b_2636_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2657_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_nat_dec_lt(v_snd_2638_, v___x_2634_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2644_; 
if (v_isShared_2641_ == 0)
{
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_fst_2637_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_snd_2638_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
else
{
uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2646_ = 0;
v___x_2647_ = lean_array_fget_borrowed(v_edited_2635_, v_snd_2638_);
v___x_2648_ = lean_box(v___x_2646_);
lean_inc(v___x_2647_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 1, v___x_2647_);
lean_ctor_set(v___x_2640_, 0, v___x_2648_);
v___x_2650_ = v___x_2640_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2647_);
v___x_2650_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = lean_array_push(v_fst_2637_, v___x_2650_);
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_nat_add(v_snd_2638_, v___x_2652_);
lean_dec(v_snd_2638_);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2651_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v_b_2636_ = v___x_2654_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_2658_, lean_object* v_edited_2659_, lean_object* v_b_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_2658_, v_edited_2659_, v_b_2660_);
lean_dec_ref(v_edited_2659_);
lean_dec(v___x_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_2662_, lean_object* v___x_2663_, lean_object* v_a_2664_, lean_object* v_b_2665_){
_start:
{
lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2692_; 
v_fst_2666_ = lean_ctor_get(v_b_2665_, 0);
v_snd_2667_ = lean_ctor_get(v_b_2665_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_b_2665_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2669_ = v_b_2665_;
v_isShared_2670_ = v_isSharedCheck_2692_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_snd_2667_);
lean_inc(v_fst_2666_);
lean_dec(v_b_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2692_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; uint8_t v___y_2673_; uint8_t v___x_2688_; 
v___x_2671_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2688_ = lean_nat_dec_lt(v_snd_2667_, v___x_2663_);
if (v___x_2688_ == 0)
{
v___y_2673_ = v___x_2688_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = lean_array_get_borrowed(v___x_2671_, v_edited_2662_, v_snd_2667_);
v___x_2690_ = lean_string_dec_eq(v___x_2689_, v_a_2664_);
if (v___x_2690_ == 0)
{
v___y_2673_ = v___x_2688_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2691_; 
lean_del_object(v___x_2669_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_fst_2666_);
lean_ctor_set(v___x_2691_, 1, v_snd_2667_);
return v___x_2691_;
}
}
v___jp_2672_:
{
if (v___y_2673_ == 0)
{
lean_object* v___x_2675_; 
if (v_isShared_2670_ == 0)
{
v___x_2675_ = v___x_2669_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_fst_2666_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_snd_2667_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
else
{
uint8_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2677_ = 0;
v___x_2678_ = lean_array_get_borrowed(v___x_2671_, v_edited_2662_, v_snd_2667_);
v___x_2679_ = lean_box(v___x_2677_);
lean_inc(v___x_2678_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v___x_2678_);
lean_ctor_set(v___x_2669_, 0, v___x_2679_);
v___x_2681_ = v___x_2669_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2679_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2678_);
v___x_2681_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_array_push(v_fst_2666_, v___x_2681_);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_nat_add(v_snd_2667_, v___x_2683_);
lean_dec(v_snd_2667_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2682_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v_b_2665_ = v___x_2685_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_2693_, lean_object* v___x_2694_, lean_object* v_a_2695_, lean_object* v_b_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_2693_, v___x_2694_, v_a_2695_, v_b_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v___x_2694_);
lean_dec_ref(v_edited_2693_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_2698_, lean_object* v___x_2699_, lean_object* v_a_2700_, lean_object* v_b_2701_){
_start:
{
lean_object* v_fst_2702_; lean_object* v_snd_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2728_; 
v_fst_2702_ = lean_ctor_get(v_b_2701_, 0);
v_snd_2703_ = lean_ctor_get(v_b_2701_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_b_2701_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2705_ = v_b_2701_;
v_isShared_2706_ = v_isSharedCheck_2728_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snd_2703_);
lean_inc(v_fst_2702_);
lean_dec(v_b_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2728_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; uint8_t v___y_2709_; uint8_t v___x_2724_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2724_ = lean_nat_dec_lt(v_snd_2703_, v___x_2699_);
if (v___x_2724_ == 0)
{
v___y_2709_ = v___x_2724_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = lean_array_get_borrowed(v___x_2707_, v_original_2698_, v_snd_2703_);
v___x_2726_ = lean_string_dec_eq(v___x_2725_, v_a_2700_);
if (v___x_2726_ == 0)
{
v___y_2709_ = v___x_2724_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2727_; 
lean_del_object(v___x_2705_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_fst_2702_);
lean_ctor_set(v___x_2727_, 1, v_snd_2703_);
return v___x_2727_;
}
}
v___jp_2708_:
{
if (v___y_2709_ == 0)
{
lean_object* v___x_2711_; 
if (v_isShared_2706_ == 0)
{
v___x_2711_ = v___x_2705_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_fst_2702_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_snd_2703_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
else
{
uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2713_ = 1;
v___x_2714_ = lean_array_get_borrowed(v___x_2707_, v_original_2698_, v_snd_2703_);
v___x_2715_ = lean_box(v___x_2713_);
lean_inc(v___x_2714_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v___x_2714_);
lean_ctor_set(v___x_2705_, 0, v___x_2715_);
v___x_2717_ = v___x_2705_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2714_);
v___x_2717_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2718_ = lean_array_push(v_fst_2702_, v___x_2717_);
v___x_2719_ = lean_unsigned_to_nat(1u);
v___x_2720_ = lean_nat_add(v_snd_2703_, v___x_2719_);
lean_dec(v_snd_2703_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2718_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v_b_2701_ = v___x_2721_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_2729_, lean_object* v___x_2730_, lean_object* v_a_2731_, lean_object* v_b_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_2729_, v___x_2730_, v_a_2731_, v_b_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v___x_2730_);
lean_dec_ref(v_original_2729_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_original_2734_, lean_object* v___x_2735_, lean_object* v_edited_2736_, lean_object* v___x_2737_, lean_object* v_as_2738_, size_t v_sz_2739_, size_t v_i_2740_, lean_object* v_b_2741_){
_start:
{
uint8_t v___x_2742_; 
v___x_2742_ = lean_usize_dec_lt(v_i_2740_, v_sz_2739_);
if (v___x_2742_ == 0)
{
return v_b_2741_;
}
else
{
lean_object* v_snd_2743_; lean_object* v_fst_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2791_; 
v_snd_2743_ = lean_ctor_get(v_b_2741_, 1);
v_fst_2744_ = lean_ctor_get(v_b_2741_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_b_2741_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2746_ = v_b_2741_;
v_isShared_2747_ = v_isSharedCheck_2791_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snd_2743_);
lean_inc(v_fst_2744_);
lean_dec(v_b_2741_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2791_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v_fst_2748_; lean_object* v_snd_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2790_; 
v_fst_2748_ = lean_ctor_get(v_snd_2743_, 0);
v_snd_2749_ = lean_ctor_get(v_snd_2743_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_snd_2743_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2751_ = v_snd_2743_;
v_isShared_2752_ = v_isSharedCheck_2790_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_snd_2749_);
lean_inc(v_fst_2748_);
lean_dec(v_snd_2743_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2790_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_a_2753_; lean_object* v___x_2755_; 
v_a_2753_ = lean_array_uget_borrowed(v_as_2738_, v_i_2740_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v_fst_2748_);
lean_ctor_set(v___x_2751_, 0, v_fst_2744_);
v___x_2755_ = v___x_2751_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_fst_2744_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_fst_2748_);
v___x_2755_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v_fst_2757_; lean_object* v_snd_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2788_; 
v___x_2756_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_2734_, v___x_2735_, v_a_2753_, v___x_2755_);
v_fst_2757_ = lean_ctor_get(v___x_2756_, 0);
v_snd_2758_ = lean_ctor_get(v___x_2756_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2760_ = v___x_2756_;
v_isShared_2761_ = v_isSharedCheck_2788_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_snd_2758_);
lean_inc(v_fst_2757_);
lean_dec(v___x_2756_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2788_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 1, v_snd_2749_);
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_fst_2757_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_snd_2749_);
v___x_2763_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2786_; 
v___x_2764_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_2736_, v___x_2737_, v_a_2753_, v___x_2763_);
v_fst_2765_ = lean_ctor_get(v___x_2764_, 0);
v_snd_2766_ = lean_ctor_get(v___x_2764_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2768_ = v___x_2764_;
v_isShared_2769_ = v_isSharedCheck_2786_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_snd_2766_);
lean_inc(v_fst_2765_);
lean_dec(v___x_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2786_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2770_ = 2;
v___x_2771_ = lean_box(v___x_2770_);
lean_inc(v_a_2753_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v_a_2753_);
lean_ctor_set(v___x_2768_, 0, v___x_2771_);
v___x_2773_ = v___x_2768_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_a_2753_);
v___x_2773_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2774_ = lean_array_push(v_fst_2765_, v___x_2773_);
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = lean_nat_add(v_snd_2758_, v___x_2775_);
lean_dec(v_snd_2758_);
v___x_2777_ = lean_nat_add(v_snd_2766_, v___x_2775_);
lean_dec(v_snd_2766_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2777_);
lean_ctor_set(v___x_2746_, 0, v___x_2776_);
v___x_2779_ = v___x_2746_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; size_t v___x_2781_; size_t v___x_2782_; 
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2774_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_add(v_i_2740_, v___x_2781_);
v_i_2740_ = v___x_2782_;
v_b_2741_ = v___x_2780_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_original_2792_, lean_object* v___x_2793_, lean_object* v_edited_2794_, lean_object* v___x_2795_, lean_object* v_as_2796_, lean_object* v_sz_2797_, lean_object* v_i_2798_, lean_object* v_b_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2797_);
lean_dec(v_sz_2797_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2798_);
lean_dec(v_i_2798_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2792_, v___x_2793_, v_edited_2794_, v___x_2795_, v_as_2796_, v_sz_boxed_2800_, v_i_boxed_2801_, v_b_2799_);
lean_dec_ref(v_as_2796_);
lean_dec(v___x_2795_);
lean_dec_ref(v_edited_2794_);
lean_dec(v___x_2793_);
lean_dec_ref(v_original_2792_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_2803_, lean_object* v___x_2804_, lean_object* v_original_2805_, lean_object* v___x_2806_, lean_object* v_as_2807_, size_t v_sz_2808_, size_t v_i_2809_, lean_object* v_b_2810_){
_start:
{
uint8_t v___x_2811_; 
v___x_2811_ = lean_usize_dec_lt(v_i_2809_, v_sz_2808_);
if (v___x_2811_ == 0)
{
return v_b_2810_;
}
else
{
lean_object* v_snd_2812_; lean_object* v_fst_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2860_; 
v_snd_2812_ = lean_ctor_get(v_b_2810_, 1);
v_fst_2813_ = lean_ctor_get(v_b_2810_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_b_2810_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2815_ = v_b_2810_;
v_isShared_2816_ = v_isSharedCheck_2860_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_snd_2812_);
lean_inc(v_fst_2813_);
lean_dec(v_b_2810_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2860_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_fst_2817_; lean_object* v_snd_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2859_; 
v_fst_2817_ = lean_ctor_get(v_snd_2812_, 0);
v_snd_2818_ = lean_ctor_get(v_snd_2812_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_snd_2812_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2820_ = v_snd_2812_;
v_isShared_2821_ = v_isSharedCheck_2859_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_snd_2818_);
lean_inc(v_fst_2817_);
lean_dec(v_snd_2812_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2859_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_a_2822_; lean_object* v___x_2824_; 
v_a_2822_ = lean_array_uget_borrowed(v_as_2807_, v_i_2809_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 1, v_fst_2817_);
lean_ctor_set(v___x_2820_, 0, v_fst_2813_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_fst_2813_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_fst_2817_);
v___x_2824_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v_fst_2826_; lean_object* v_snd_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2857_; 
v___x_2825_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_2805_, v___x_2806_, v_a_2822_, v___x_2824_);
v_fst_2826_ = lean_ctor_get(v___x_2825_, 0);
v_snd_2827_ = lean_ctor_get(v___x_2825_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2829_ = v___x_2825_;
v_isShared_2830_ = v_isSharedCheck_2857_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_snd_2827_);
lean_inc(v_fst_2826_);
lean_dec(v___x_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2857_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_snd_2818_);
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_fst_2826_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_snd_2818_);
v___x_2832_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2855_; 
v___x_2833_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_2803_, v___x_2804_, v_a_2822_, v___x_2832_);
v_fst_2834_ = lean_ctor_get(v___x_2833_, 0);
v_snd_2835_ = lean_ctor_get(v___x_2833_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2837_ = v___x_2833_;
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snd_2835_);
lean_inc(v_fst_2834_);
lean_dec(v___x_2833_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
uint8_t v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2839_ = 2;
v___x_2840_ = lean_box(v___x_2839_);
lean_inc(v_a_2822_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_a_2822_);
lean_ctor_set(v___x_2837_, 0, v___x_2840_);
v___x_2842_ = v___x_2837_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_a_2822_);
v___x_2842_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2843_ = lean_array_push(v_fst_2834_, v___x_2842_);
v___x_2844_ = lean_unsigned_to_nat(1u);
v___x_2845_ = lean_nat_add(v_snd_2827_, v___x_2844_);
lean_dec(v_snd_2827_);
v___x_2846_ = lean_nat_add(v_snd_2835_, v___x_2844_);
lean_dec(v_snd_2835_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v___x_2846_);
lean_ctor_set(v___x_2815_, 0, v___x_2845_);
v___x_2848_ = v___x_2815_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2843_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_i_2809_, v___x_2850_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2805_, v___x_2806_, v_edited_2803_, v___x_2804_, v_as_2807_, v_sz_2808_, v___x_2851_, v___x_2849_);
return v___x_2852_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_2861_, lean_object* v___x_2862_, lean_object* v_original_2863_, lean_object* v___x_2864_, lean_object* v_as_2865_, lean_object* v_sz_2866_, lean_object* v_i_2867_, lean_object* v_b_2868_){
_start:
{
size_t v_sz_boxed_2869_; size_t v_i_boxed_2870_; lean_object* v_res_2871_; 
v_sz_boxed_2869_ = lean_unbox_usize(v_sz_2866_);
lean_dec(v_sz_2866_);
v_i_boxed_2870_ = lean_unbox_usize(v_i_2867_);
lean_dec(v_i_2867_);
v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_2861_, v___x_2862_, v_original_2863_, v___x_2864_, v_as_2865_, v_sz_boxed_2869_, v_i_boxed_2870_, v_b_2868_);
lean_dec_ref(v_as_2865_);
lean_dec(v___x_2864_);
lean_dec_ref(v_original_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_edited_2861_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_box(0);
return v___x_2874_;
}
else
{
lean_object* v_key_2875_; lean_object* v_value_2876_; lean_object* v_tail_2877_; uint8_t v___x_2878_; 
v_key_2875_ = lean_ctor_get(v_x_2873_, 0);
v_value_2876_ = lean_ctor_get(v_x_2873_, 1);
v_tail_2877_ = lean_ctor_get(v_x_2873_, 2);
v___x_2878_ = lean_string_dec_eq(v_key_2875_, v_a_2872_);
if (v___x_2878_ == 0)
{
v_x_2873_ = v_tail_2877_;
goto _start;
}
else
{
lean_object* v___x_2880_; 
lean_inc(v_value_2876_);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_value_2876_);
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2881_, lean_object* v_x_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2881_, v_x_2882_);
lean_dec(v_x_2882_);
lean_dec_ref(v_a_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_buckets_2886_; lean_object* v___x_2887_; uint64_t v___x_2888_; uint64_t v___x_2889_; uint64_t v___x_2890_; uint64_t v_fold_2891_; uint64_t v___x_2892_; uint64_t v___x_2893_; uint64_t v___x_2894_; size_t v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_buckets_2886_ = lean_ctor_get(v_m_2884_, 1);
v___x_2887_ = lean_array_get_size(v_buckets_2886_);
v___x_2888_ = lean_string_hash(v_a_2885_);
v___x_2889_ = 32ULL;
v___x_2890_ = lean_uint64_shift_right(v___x_2888_, v___x_2889_);
v_fold_2891_ = lean_uint64_xor(v___x_2888_, v___x_2890_);
v___x_2892_ = 16ULL;
v___x_2893_ = lean_uint64_shift_right(v_fold_2891_, v___x_2892_);
v___x_2894_ = lean_uint64_xor(v_fold_2891_, v___x_2893_);
v___x_2895_ = lean_uint64_to_usize(v___x_2894_);
v___x_2896_ = lean_usize_of_nat(v___x_2887_);
v___x_2897_ = ((size_t)1ULL);
v___x_2898_ = lean_usize_sub(v___x_2896_, v___x_2897_);
v___x_2899_ = lean_usize_land(v___x_2895_, v___x_2898_);
v___x_2900_ = lean_array_uget_borrowed(v_buckets_2886_, v___x_2899_);
v___x_2901_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2885_, v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2902_, v_a_2903_);
lean_dec_ref(v_a_2903_);
lean_dec_ref(v_m_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2905_, lean_object* v_b_2906_, lean_object* v_x_2907_){
_start:
{
if (lean_obj_tag(v_x_2907_) == 0)
{
lean_dec(v_b_2906_);
lean_dec_ref(v_a_2905_);
return v_x_2907_;
}
else
{
lean_object* v_key_2908_; lean_object* v_value_2909_; lean_object* v_tail_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2922_; 
v_key_2908_ = lean_ctor_get(v_x_2907_, 0);
v_value_2909_ = lean_ctor_get(v_x_2907_, 1);
v_tail_2910_ = lean_ctor_get(v_x_2907_, 2);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_x_2907_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2912_ = v_x_2907_;
v_isShared_2913_ = v_isSharedCheck_2922_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_tail_2910_);
lean_inc(v_value_2909_);
lean_inc(v_key_2908_);
lean_dec(v_x_2907_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2922_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
uint8_t v___x_2914_; 
v___x_2914_ = lean_string_dec_eq(v_key_2908_, v_a_2905_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2905_, v_b_2906_, v_tail_2910_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 2, v___x_2915_);
v___x_2917_ = v___x_2912_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_key_2908_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_value_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
else
{
lean_object* v___x_2920_; 
lean_dec(v_value_2909_);
lean_dec(v_key_2908_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v_b_2906_);
lean_ctor_set(v___x_2912_, 0, v_a_2905_);
v___x_2920_ = v___x_2912_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2905_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_b_2906_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v_tail_2910_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2923_, lean_object* v_x_2924_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = 0;
return v___x_2925_;
}
else
{
lean_object* v_key_2926_; lean_object* v_tail_2927_; uint8_t v___x_2928_; 
v_key_2926_ = lean_ctor_get(v_x_2924_, 0);
v_tail_2927_ = lean_ctor_get(v_x_2924_, 2);
v___x_2928_ = lean_string_dec_eq(v_key_2926_, v_a_2923_);
if (v___x_2928_ == 0)
{
v_x_2924_ = v_tail_2927_;
goto _start;
}
else
{
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2930_, lean_object* v_x_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2930_, v_x_2931_);
lean_dec(v_x_2931_);
lean_dec_ref(v_a_2930_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
return v_x_2934_;
}
else
{
lean_object* v_key_2936_; lean_object* v_value_2937_; lean_object* v_tail_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2961_; 
v_key_2936_ = lean_ctor_get(v_x_2935_, 0);
v_value_2937_ = lean_ctor_get(v_x_2935_, 1);
v_tail_2938_ = lean_ctor_get(v_x_2935_, 2);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_x_2935_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2940_ = v_x_2935_;
v_isShared_2941_ = v_isSharedCheck_2961_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_tail_2938_);
lean_inc(v_value_2937_);
lean_inc(v_key_2936_);
lean_dec(v_x_2935_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2961_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; uint64_t v___x_2943_; uint64_t v___x_2944_; uint64_t v___x_2945_; uint64_t v_fold_2946_; uint64_t v___x_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; size_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2942_ = lean_array_get_size(v_x_2934_);
v___x_2943_ = lean_string_hash(v_key_2936_);
v___x_2944_ = 32ULL;
v___x_2945_ = lean_uint64_shift_right(v___x_2943_, v___x_2944_);
v_fold_2946_ = lean_uint64_xor(v___x_2943_, v___x_2945_);
v___x_2947_ = 16ULL;
v___x_2948_ = lean_uint64_shift_right(v_fold_2946_, v___x_2947_);
v___x_2949_ = lean_uint64_xor(v_fold_2946_, v___x_2948_);
v___x_2950_ = lean_uint64_to_usize(v___x_2949_);
v___x_2951_ = lean_usize_of_nat(v___x_2942_);
v___x_2952_ = ((size_t)1ULL);
v___x_2953_ = lean_usize_sub(v___x_2951_, v___x_2952_);
v___x_2954_ = lean_usize_land(v___x_2950_, v___x_2953_);
v___x_2955_ = lean_array_uget_borrowed(v_x_2934_, v___x_2954_);
lean_inc(v___x_2955_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 2, v___x_2955_);
v___x_2957_ = v___x_2940_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_key_2936_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_value_2937_);
lean_ctor_set(v_reuseFailAlloc_2960_, 2, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_array_uset(v_x_2934_, v___x_2954_, v___x_2957_);
v_x_2934_ = v___x_2958_;
v_x_2935_ = v_tail_2938_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2962_, lean_object* v_source_2963_, lean_object* v_target_2964_){
_start:
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = lean_array_get_size(v_source_2963_);
v___x_2966_ = lean_nat_dec_lt(v_i_2962_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec_ref(v_source_2963_);
lean_dec(v_i_2962_);
return v_target_2964_;
}
else
{
lean_object* v_es_2967_; lean_object* v___x_2968_; lean_object* v_source_2969_; lean_object* v_target_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_es_2967_ = lean_array_fget(v_source_2963_, v_i_2962_);
v___x_2968_ = lean_box(0);
v_source_2969_ = lean_array_fset(v_source_2963_, v_i_2962_, v___x_2968_);
v_target_2970_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2964_, v_es_2967_);
v___x_2971_ = lean_unsigned_to_nat(1u);
v___x_2972_ = lean_nat_add(v_i_2962_, v___x_2971_);
lean_dec(v_i_2962_);
v_i_2962_ = v___x_2972_;
v_source_2963_ = v_source_2969_;
v_target_2964_ = v_target_2970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2974_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_nbuckets_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2975_ = lean_array_get_size(v_data_2974_);
v___x_2976_ = lean_unsigned_to_nat(2u);
v_nbuckets_2977_ = lean_nat_mul(v___x_2975_, v___x_2976_);
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_mk_array(v_nbuckets_2977_, v___x_2979_);
v___x_2981_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2978_, v_data_2974_, v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2982_, lean_object* v_a_2983_, lean_object* v_b_2984_){
_start:
{
lean_object* v_size_2985_; lean_object* v_buckets_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3029_; 
v_size_2985_ = lean_ctor_get(v_m_2982_, 0);
v_buckets_2986_ = lean_ctor_get(v_m_2982_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_m_2982_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_2988_ = v_m_2982_;
v_isShared_2989_ = v_isSharedCheck_3029_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_buckets_2986_);
lean_inc(v_size_2985_);
lean_dec(v_m_2982_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3029_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; uint64_t v___x_2991_; uint64_t v___x_2992_; uint64_t v___x_2993_; uint64_t v_fold_2994_; uint64_t v___x_2995_; uint64_t v___x_2996_; uint64_t v___x_2997_; size_t v___x_2998_; size_t v___x_2999_; size_t v___x_3000_; size_t v___x_3001_; size_t v___x_3002_; lean_object* v_bkt_3003_; uint8_t v___x_3004_; 
v___x_2990_ = lean_array_get_size(v_buckets_2986_);
v___x_2991_ = lean_string_hash(v_a_2983_);
v___x_2992_ = 32ULL;
v___x_2993_ = lean_uint64_shift_right(v___x_2991_, v___x_2992_);
v_fold_2994_ = lean_uint64_xor(v___x_2991_, v___x_2993_);
v___x_2995_ = 16ULL;
v___x_2996_ = lean_uint64_shift_right(v_fold_2994_, v___x_2995_);
v___x_2997_ = lean_uint64_xor(v_fold_2994_, v___x_2996_);
v___x_2998_ = lean_uint64_to_usize(v___x_2997_);
v___x_2999_ = lean_usize_of_nat(v___x_2990_);
v___x_3000_ = ((size_t)1ULL);
v___x_3001_ = lean_usize_sub(v___x_2999_, v___x_3000_);
v___x_3002_ = lean_usize_land(v___x_2998_, v___x_3001_);
v_bkt_3003_ = lean_array_uget_borrowed(v_buckets_2986_, v___x_3002_);
v___x_3004_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2983_, v_bkt_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v_size_x27_3006_; lean_object* v___x_3007_; lean_object* v_buckets_x27_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3005_ = lean_unsigned_to_nat(1u);
v_size_x27_3006_ = lean_nat_add(v_size_2985_, v___x_3005_);
lean_dec(v_size_2985_);
lean_inc(v_bkt_3003_);
v___x_3007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3007_, 0, v_a_2983_);
lean_ctor_set(v___x_3007_, 1, v_b_2984_);
lean_ctor_set(v___x_3007_, 2, v_bkt_3003_);
v_buckets_x27_3008_ = lean_array_uset(v_buckets_2986_, v___x_3002_, v___x_3007_);
v___x_3009_ = lean_unsigned_to_nat(4u);
v___x_3010_ = lean_nat_mul(v_size_x27_3006_, v___x_3009_);
v___x_3011_ = lean_unsigned_to_nat(3u);
v___x_3012_ = lean_nat_div(v___x_3010_, v___x_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_array_get_size(v_buckets_x27_3008_);
v___x_3014_ = lean_nat_dec_le(v___x_3012_, v___x_3013_);
lean_dec(v___x_3012_);
if (v___x_3014_ == 0)
{
lean_object* v_val_3015_; lean_object* v___x_3017_; 
v_val_3015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_3008_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v_val_3015_);
lean_ctor_set(v___x_2988_, 0, v_size_x27_3006_);
v___x_3017_ = v___x_2988_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_size_x27_3006_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_val_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
else
{
lean_object* v___x_3020_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v_buckets_x27_3008_);
lean_ctor_set(v___x_2988_, 0, v_size_x27_3006_);
v___x_3020_ = v___x_2988_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_size_x27_3006_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_buckets_x27_3008_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v___x_3022_; lean_object* v_buckets_x27_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
lean_inc(v_bkt_3003_);
v___x_3022_ = lean_box(0);
v_buckets_x27_3023_ = lean_array_uset(v_buckets_2986_, v___x_3002_, v___x_3022_);
v___x_3024_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2983_, v_b_2984_, v_bkt_3003_);
v___x_3025_ = lean_array_uset(v_buckets_x27_3023_, v___x_3002_, v___x_3024_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v___x_3025_);
v___x_3027_ = v___x_2988_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_size_2985_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_3030_, lean_object* v_index_3031_, lean_object* v_val_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3030_, v_val_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3034_ = lean_unsigned_to_nat(1u);
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_index_3031_);
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3034_);
lean_ctor_set(v___x_3038_, 1, v___x_3035_);
lean_ctor_set(v___x_3038_, 2, v___x_3036_);
lean_ctor_set(v___x_3038_, 3, v___x_3037_);
v___x_3039_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3030_, v_val_3032_, v___x_3038_);
return v___x_3039_;
}
else
{
lean_object* v_val_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3061_; 
v_val_3040_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3042_ = v___x_3033_;
v_isShared_3043_ = v_isSharedCheck_3061_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_val_3040_);
lean_dec(v___x_3033_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3061_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_leftCount_3044_; lean_object* v_rightCount_3045_; lean_object* v_rightIndex_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3059_; 
v_leftCount_3044_ = lean_ctor_get(v_val_3040_, 0);
v_rightCount_3045_ = lean_ctor_get(v_val_3040_, 2);
v_rightIndex_3046_ = lean_ctor_get(v_val_3040_, 3);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_val_3040_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v_val_3040_, 1);
lean_dec(v_unused_3060_);
v___x_3048_ = v_val_3040_;
v_isShared_3049_ = v_isSharedCheck_3059_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_rightIndex_3046_);
lean_inc(v_rightCount_3045_);
lean_inc(v_leftCount_3044_);
lean_dec(v_val_3040_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3059_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_add(v_leftCount_3044_, v___x_3050_);
lean_dec(v_leftCount_3044_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v_index_3031_);
v___x_3053_ = v___x_3042_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_index_3031_);
v___x_3053_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3055_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v___x_3053_);
lean_ctor_set(v___x_3048_, 0, v___x_3051_);
v___x_3055_ = v___x_3048_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v_rightCount_3045_);
lean_ctor_set(v_reuseFailAlloc_3057_, 3, v_rightIndex_3046_);
v___x_3055_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3030_, v_val_3032_, v___x_3055_);
return v___x_3056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3062_, lean_object* v_fst_3063_, lean_object* v___x_3064_, lean_object* v_fst_3065_, lean_object* v_a_3066_, lean_object* v_b_3067_){
_start:
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_nat_dec_lt(v_a_3066_, v_upperBound_3062_);
if (v___x_3068_ == 0)
{
lean_dec(v_a_3066_);
return v_b_3067_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = l_Subarray_get___redArg(v_fst_3065_, v_a_3066_);
lean_inc(v_a_3066_);
v___x_3070_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3067_, v_a_3066_, v___x_3069_);
v___x_3071_ = lean_unsigned_to_nat(1u);
v___x_3072_ = lean_nat_add(v_a_3066_, v___x_3071_);
lean_dec(v_a_3066_);
v_a_3066_ = v___x_3072_;
v_b_3067_ = v___x_3070_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3074_, lean_object* v_fst_3075_, lean_object* v___x_3076_, lean_object* v_fst_3077_, lean_object* v_a_3078_, lean_object* v_b_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3074_, v_fst_3075_, v___x_3076_, v_fst_3077_, v_a_3078_, v_b_3079_);
lean_dec_ref(v_fst_3077_);
lean_dec(v___x_3076_);
lean_dec_ref(v_fst_3075_);
lean_dec(v_upperBound_3074_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3081_, lean_object* v_x_3082_){
_start:
{
if (lean_obj_tag(v_x_3082_) == 0)
{
lean_inc(v_x_3081_);
return v_x_3081_;
}
else
{
lean_object* v_key_3083_; lean_object* v_value_3084_; lean_object* v_tail_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_key_3083_ = lean_ctor_get(v_x_3082_, 0);
v_value_3084_ = lean_ctor_get(v_x_3082_, 1);
v_tail_3085_ = lean_ctor_get(v_x_3082_, 2);
v___x_3086_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3081_, v_tail_3085_);
lean_inc(v_value_3084_);
lean_inc(v_key_3083_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v_key_3083_);
lean_ctor_set(v___x_3087_, 1, v_value_3084_);
v___x_3088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___x_3086_);
return v___x_3088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3089_, lean_object* v_x_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3089_, v_x_3090_);
lean_dec(v_x_3090_);
lean_dec(v_x_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3092_, size_t v_i_3093_, size_t v_stop_3094_, lean_object* v_b_3095_){
_start:
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_usize_dec_eq(v_i_3093_, v_stop_3094_);
if (v___x_3096_ == 0)
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3097_ = ((size_t)1ULL);
v___x_3098_ = lean_usize_sub(v_i_3093_, v___x_3097_);
v___x_3099_ = lean_array_uget_borrowed(v_as_3092_, v___x_3098_);
v___x_3100_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3095_, v___x_3099_);
lean_dec(v_b_3095_);
v_i_3093_ = v___x_3098_;
v_b_3095_ = v___x_3100_;
goto _start;
}
else
{
return v_b_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3102_, lean_object* v_i_3103_, lean_object* v_stop_3104_, lean_object* v_b_3105_){
_start:
{
size_t v_i_boxed_3106_; size_t v_stop_boxed_3107_; lean_object* v_res_3108_; 
v_i_boxed_3106_ = lean_unbox_usize(v_i_3103_);
lean_dec(v_i_3103_);
v_stop_boxed_3107_ = lean_unbox_usize(v_stop_3104_);
lean_dec(v_stop_3104_);
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3102_, v_i_boxed_3106_, v_stop_boxed_3107_, v_b_3105_);
lean_dec_ref(v_as_3102_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3109_, lean_object* v_right_3110_, lean_object* v_pref_3111_){
_start:
{
lean_object* v_start_3112_; lean_object* v_stop_3113_; lean_object* v_i_3114_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v_start_3112_ = lean_ctor_get(v_left_3109_, 1);
v_stop_3113_ = lean_ctor_get(v_left_3109_, 2);
v_i_3114_ = lean_array_get_size(v_pref_3111_);
v___x_3120_ = lean_nat_sub(v_stop_3113_, v_start_3112_);
v___x_3121_ = lean_nat_dec_lt(v_i_3114_, v___x_3120_);
lean_dec(v___x_3120_);
if (v___x_3121_ == 0)
{
goto v___jp_3115_;
}
else
{
lean_object* v_start_3122_; lean_object* v_stop_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v_start_3122_ = lean_ctor_get(v_right_3110_, 1);
v_stop_3123_ = lean_ctor_get(v_right_3110_, 2);
v___x_3124_ = lean_nat_sub(v_stop_3123_, v_start_3122_);
v___x_3125_ = lean_nat_dec_lt(v_i_3114_, v___x_3124_);
lean_dec(v___x_3124_);
if (v___x_3125_ == 0)
{
goto v___jp_3115_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3126_ = l_Subarray_get___redArg(v_left_3109_, v_i_3114_);
v___x_3127_ = l_Subarray_get___redArg(v_right_3110_, v_i_3114_);
v___x_3128_ = lean_string_dec_eq(v___x_3126_, v___x_3127_);
lean_dec(v___x_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec(v___x_3126_);
v___x_3129_ = l_Subarray_drop___redArg(v_left_3109_, v_i_3114_);
v___x_3130_ = l_Subarray_drop___redArg(v_right_3110_, v_i_3114_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_pref_3111_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_array_push(v_pref_3111_, v___x_3126_);
v_pref_3111_ = v___x_3133_;
goto _start;
}
}
}
v___jp_3115_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3116_ = l_Subarray_drop___redArg(v_left_3109_, v_i_3114_);
v___x_3117_ = l_Subarray_drop___redArg(v_right_3110_, v_i_3114_);
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3116_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_pref_3111_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
return v___x_3119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3137_, lean_object* v_right_3138_){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3140_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3137_, v_right_3138_, v___x_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3141_, lean_object* v_b_3142_){
_start:
{
lean_object* v_array_3143_; lean_object* v_start_3144_; lean_object* v_stop_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3158_; 
v_array_3143_ = lean_ctor_get(v_a_3141_, 0);
v_start_3144_ = lean_ctor_get(v_a_3141_, 1);
v_stop_3145_ = lean_ctor_get(v_a_3141_, 2);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_a_3141_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3147_ = v_a_3141_;
v_isShared_3148_ = v_isSharedCheck_3158_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_stop_3145_);
lean_inc(v_start_3144_);
lean_inc(v_array_3143_);
lean_dec(v_a_3141_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3158_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_nat_dec_lt(v_start_3144_, v_stop_3145_);
if (v___x_3149_ == 0)
{
lean_del_object(v___x_3147_);
lean_dec(v_stop_3145_);
lean_dec(v_start_3144_);
lean_dec_ref(v_array_3143_);
return v_b_3142_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3150_ = lean_unsigned_to_nat(1u);
v___x_3151_ = lean_nat_add(v_start_3144_, v___x_3150_);
lean_inc_ref(v_array_3143_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 1, v___x_3151_);
v___x_3153_ = v___x_3147_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_array_3143_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_stop_3145_);
v___x_3153_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_array_fget(v_array_3143_, v_start_3144_);
lean_dec(v_start_3144_);
lean_dec_ref(v_array_3143_);
v___x_3155_ = lean_array_push(v_b_3142_, v___x_3154_);
v_a_3141_ = v___x_3153_;
v_b_3142_ = v___x_3155_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3159_, lean_object* v_right_3160_, lean_object* v_i_3161_){
_start:
{
lean_object* v_start_3162_; lean_object* v_stop_3163_; lean_object* v___x_3164_; uint8_t v___x_3178_; 
v_start_3162_ = lean_ctor_get(v_left_3159_, 1);
v_stop_3163_ = lean_ctor_get(v_left_3159_, 2);
v___x_3164_ = lean_nat_sub(v_stop_3163_, v_start_3162_);
v___x_3178_ = lean_nat_dec_lt(v_i_3161_, v___x_3164_);
if (v___x_3178_ == 0)
{
goto v___jp_3165_;
}
else
{
lean_object* v_start_3179_; lean_object* v_stop_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v_start_3179_ = lean_ctor_get(v_right_3160_, 1);
v_stop_3180_ = lean_ctor_get(v_right_3160_, 2);
v___x_3181_ = lean_nat_sub(v_stop_3180_, v_start_3179_);
v___x_3182_ = lean_nat_dec_lt(v_i_3161_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_dec(v___x_3181_);
goto v___jp_3165_;
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3183_ = lean_nat_sub(v___x_3164_, v_i_3161_);
lean_dec(v___x_3164_);
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = lean_nat_sub(v___x_3183_, v___x_3184_);
v___x_3186_ = l_Subarray_get___redArg(v_left_3159_, v___x_3185_);
lean_dec(v___x_3185_);
v___x_3187_ = lean_nat_sub(v___x_3181_, v_i_3161_);
lean_dec(v___x_3181_);
v___x_3188_ = lean_nat_sub(v___x_3187_, v___x_3184_);
v___x_3189_ = l_Subarray_get___redArg(v_right_3160_, v___x_3188_);
lean_dec(v___x_3188_);
v___x_3190_ = lean_string_dec_eq(v___x_3186_, v___x_3189_);
lean_dec(v___x_3189_);
lean_dec(v___x_3186_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec(v_i_3161_);
lean_inc_ref(v_left_3159_);
v___x_3191_ = l_Subarray_take___redArg(v_left_3159_, v___x_3183_);
v___x_3192_ = l_Subarray_take___redArg(v_right_3160_, v___x_3187_);
lean_dec(v___x_3187_);
v___x_3193_ = l_Subarray_drop___redArg(v_left_3159_, v___x_3183_);
lean_dec(v___x_3183_);
v___x_3194_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3195_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3193_, v___x_3194_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3192_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3191_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; 
lean_dec(v___x_3187_);
lean_dec(v___x_3183_);
v___x_3198_ = lean_nat_add(v_i_3161_, v___x_3184_);
lean_dec(v_i_3161_);
v_i_3161_ = v___x_3198_;
goto _start;
}
}
}
v___jp_3165_:
{
lean_object* v_start_3166_; lean_object* v_stop_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_start_3166_ = lean_ctor_get(v_right_3160_, 1);
v_stop_3167_ = lean_ctor_get(v_right_3160_, 2);
v___x_3168_ = lean_nat_sub(v___x_3164_, v_i_3161_);
lean_dec(v___x_3164_);
lean_inc_ref(v_left_3159_);
v___x_3169_ = l_Subarray_take___redArg(v_left_3159_, v___x_3168_);
v___x_3170_ = lean_nat_sub(v_stop_3167_, v_start_3166_);
v___x_3171_ = lean_nat_sub(v___x_3170_, v_i_3161_);
lean_dec(v_i_3161_);
lean_dec(v___x_3170_);
v___x_3172_ = l_Subarray_take___redArg(v_right_3160_, v___x_3171_);
lean_dec(v___x_3171_);
v___x_3173_ = l_Subarray_drop___redArg(v_left_3159_, v___x_3168_);
lean_dec(v___x_3168_);
v___x_3174_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3175_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3173_, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3172_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3169_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3200_, lean_object* v_right_3201_){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3200_, v_right_3201_, v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3204_, lean_object* v_b_3205_){
_start:
{
if (lean_obj_tag(v_as_x27_3204_) == 0)
{
return v_b_3205_;
}
else
{
lean_object* v_head_3206_; lean_object* v_snd_3207_; lean_object* v_leftIndex_3208_; 
v_head_3206_ = lean_ctor_get(v_as_x27_3204_, 0);
v_snd_3207_ = lean_ctor_get(v_head_3206_, 1);
v_leftIndex_3208_ = lean_ctor_get(v_snd_3207_, 1);
if (lean_obj_tag(v_leftIndex_3208_) == 1)
{
lean_object* v_rightIndex_3209_; 
v_rightIndex_3209_ = lean_ctor_get(v_snd_3207_, 3);
if (lean_obj_tag(v_rightIndex_3209_) == 1)
{
if (lean_obj_tag(v_b_3205_) == 0)
{
lean_object* v_tail_3210_; lean_object* v_fst_3211_; lean_object* v_leftCount_3212_; lean_object* v_rightCount_3213_; lean_object* v_val_3214_; lean_object* v_val_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_tail_3210_ = lean_ctor_get(v_as_x27_3204_, 1);
v_fst_3211_ = lean_ctor_get(v_head_3206_, 0);
v_leftCount_3212_ = lean_ctor_get(v_snd_3207_, 0);
v_rightCount_3213_ = lean_ctor_get(v_snd_3207_, 2);
v_val_3214_ = lean_ctor_get(v_leftIndex_3208_, 0);
v_val_3215_ = lean_ctor_get(v_rightIndex_3209_, 0);
v___x_3216_ = lean_nat_add(v_leftCount_3212_, v_rightCount_3213_);
lean_inc(v_val_3215_);
lean_inc(v_val_3214_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v_val_3214_);
lean_ctor_set(v___x_3217_, 1, v_val_3215_);
lean_inc(v_fst_3211_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v_fst_3211_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3216_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
v_as_x27_3204_ = v_tail_3210_;
v_b_3205_ = v___x_3220_;
goto _start;
}
else
{
lean_object* v_val_3222_; lean_object* v_tail_3223_; lean_object* v_fst_3224_; lean_object* v_leftCount_3225_; lean_object* v_rightCount_3226_; lean_object* v_val_3227_; lean_object* v_val_3228_; lean_object* v_fst_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3250_; 
v_val_3222_ = lean_ctor_get(v_b_3205_, 0);
lean_inc(v_val_3222_);
v_tail_3223_ = lean_ctor_get(v_as_x27_3204_, 1);
v_fst_3224_ = lean_ctor_get(v_head_3206_, 0);
v_leftCount_3225_ = lean_ctor_get(v_snd_3207_, 0);
v_rightCount_3226_ = lean_ctor_get(v_snd_3207_, 2);
v_val_3227_ = lean_ctor_get(v_leftIndex_3208_, 0);
v_val_3228_ = lean_ctor_get(v_rightIndex_3209_, 0);
v_fst_3229_ = lean_ctor_get(v_val_3222_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_val_3222_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_val_3222_, 1);
lean_dec(v_unused_3251_);
v___x_3231_ = v_val_3222_;
v_isShared_3232_ = v_isSharedCheck_3250_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_fst_3229_);
lean_dec(v_val_3222_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3250_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = lean_nat_add(v_leftCount_3225_, v_rightCount_3226_);
v___x_3234_ = lean_nat_dec_lt(v___x_3233_, v_fst_3229_);
lean_dec(v_fst_3229_);
if (v___x_3234_ == 0)
{
lean_dec(v___x_3233_);
lean_del_object(v___x_3231_);
v_as_x27_3204_ = v_tail_3223_;
goto _start;
}
else
{
lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3248_; 
v_isSharedCheck_3248_ = !lean_is_exclusive(v_b_3205_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; 
v_unused_3249_ = lean_ctor_get(v_b_3205_, 0);
lean_dec(v_unused_3249_);
v___x_3237_ = v_b_3205_;
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
else
{
lean_dec(v_b_3205_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
lean_inc(v_val_3228_);
lean_inc(v_val_3227_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v_val_3228_);
lean_ctor_set(v___x_3231_, 0, v_val_3227_);
v___x_3240_ = v___x_3231_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_val_3227_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_val_3228_);
v___x_3240_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_inc(v_fst_3224_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_fst_3224_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3233_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3242_);
v___x_3244_ = v___x_3237_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
v_as_x27_3204_ = v_tail_3223_;
v_b_3205_ = v___x_3244_;
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
lean_object* v_tail_3252_; 
v_tail_3252_ = lean_ctor_get(v_as_x27_3204_, 1);
v_as_x27_3204_ = v_tail_3252_;
goto _start;
}
}
else
{
lean_object* v_tail_3254_; 
v_tail_3254_ = lean_ctor_get(v_as_x27_3204_, 1);
v_as_x27_3204_ = v_tail_3254_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_as_x27_3256_, lean_object* v_b_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3256_, v_b_3257_);
lean_dec(v_as_x27_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3259_, lean_object* v_index_3260_, lean_object* v_val_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3259_, v_val_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = lean_box(0);
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_index_3260_);
v___x_3267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3263_);
lean_ctor_set(v___x_3267_, 1, v___x_3264_);
lean_ctor_set(v___x_3267_, 2, v___x_3265_);
lean_ctor_set(v___x_3267_, 3, v___x_3266_);
v___x_3268_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3259_, v_val_3261_, v___x_3267_);
return v___x_3268_;
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3290_; 
v_val_3269_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3271_ = v___x_3262_;
v_isShared_3272_ = v_isSharedCheck_3290_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_val_3269_);
lean_dec(v___x_3262_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3290_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_leftCount_3273_; lean_object* v_leftIndex_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3287_; 
v_leftCount_3273_ = lean_ctor_get(v_val_3269_, 0);
v_leftIndex_3274_ = lean_ctor_get(v_val_3269_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_val_3269_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; lean_object* v_unused_3289_; 
v_unused_3288_ = lean_ctor_get(v_val_3269_, 3);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_val_3269_, 2);
lean_dec(v_unused_3289_);
v___x_3276_ = v_val_3269_;
v_isShared_3277_ = v_isSharedCheck_3287_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_leftIndex_3274_);
lean_inc(v_leftCount_3273_);
lean_dec(v_val_3269_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3287_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = lean_nat_add(v_leftCount_3273_, v___x_3278_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v_index_3260_);
v___x_3281_ = v___x_3271_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_index_3260_);
v___x_3281_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3283_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 3, v___x_3281_);
lean_ctor_set(v___x_3276_, 2, v___x_3279_);
v___x_3283_ = v___x_3276_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_leftCount_3273_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_leftIndex_3274_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3285_, 3, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3259_, v_val_3261_, v___x_3283_);
return v___x_3284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3291_, lean_object* v___x_3292_, lean_object* v_fst_3293_, lean_object* v___x_3294_, lean_object* v_a_3295_, lean_object* v_b_3296_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_nat_dec_lt(v_a_3295_, v_upperBound_3291_);
if (v___x_3297_ == 0)
{
lean_dec(v_a_3295_);
return v_b_3296_;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3298_ = l_Subarray_get___redArg(v_fst_3293_, v_a_3295_);
lean_inc(v_a_3295_);
v___x_3299_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3296_, v_a_3295_, v___x_3298_);
v___x_3300_ = lean_unsigned_to_nat(1u);
v___x_3301_ = lean_nat_add(v_a_3295_, v___x_3300_);
lean_dec(v_a_3295_);
v_a_3295_ = v___x_3301_;
v_b_3296_ = v___x_3299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3303_, lean_object* v___x_3304_, lean_object* v_fst_3305_, lean_object* v___x_3306_, lean_object* v_a_3307_, lean_object* v_b_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3303_, v___x_3304_, v_fst_3305_, v___x_3306_, v_a_3307_, v_b_3308_);
lean_dec(v___x_3306_);
lean_dec_ref(v_fst_3305_);
lean_dec(v___x_3304_);
lean_dec(v_upperBound_3303_);
return v_res_3309_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_unsigned_to_nat(16u);
v___x_3312_ = lean_mk_array(v___x_3311_, v___x_3310_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v_hist_3315_; 
v___x_3313_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3314_ = lean_unsigned_to_nat(0u);
v_hist_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3315_, 0, v___x_3314_);
lean_ctor_set(v_hist_3315_, 1, v___x_3313_);
return v_hist_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3316_, lean_object* v_right_3317_){
_start:
{
lean_object* v___x_3318_; lean_object* v_snd_3319_; lean_object* v_fst_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3323_; lean_object* v_snd_3324_; lean_object* v_fst_3325_; lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v_start_3328_; lean_object* v_stop_3329_; lean_object* v___x_3330_; lean_object* v_hist_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v_start_3334_; lean_object* v_stop_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_buckets_3338_; lean_object* v___x_3339_; lean_object* v___y_3341_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3318_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3316_, v_right_3317_);
v_snd_3319_ = lean_ctor_get(v___x_3318_, 1);
lean_inc(v_snd_3319_);
v_fst_3320_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_fst_3320_);
lean_dec_ref(v___x_3318_);
v_fst_3321_ = lean_ctor_get(v_snd_3319_, 0);
lean_inc(v_fst_3321_);
v_snd_3322_ = lean_ctor_get(v_snd_3319_, 1);
lean_inc(v_snd_3322_);
lean_dec(v_snd_3319_);
v___x_3323_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3321_, v_snd_3322_);
v_snd_3324_ = lean_ctor_get(v___x_3323_, 1);
lean_inc(v_snd_3324_);
v_fst_3325_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_fst_3325_);
lean_dec_ref(v___x_3323_);
v_fst_3326_ = lean_ctor_get(v_snd_3324_, 0);
lean_inc(v_fst_3326_);
v_snd_3327_ = lean_ctor_get(v_snd_3324_, 1);
lean_inc(v_snd_3327_);
lean_dec(v_snd_3324_);
v_start_3328_ = lean_ctor_get(v_fst_3325_, 1);
v_stop_3329_ = lean_ctor_get(v_fst_3325_, 2);
v___x_3330_ = lean_unsigned_to_nat(0u);
v_hist_3331_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3332_ = lean_nat_sub(v_stop_3329_, v_start_3328_);
v___x_3333_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3332_, v_fst_3326_, v___x_3332_, v_fst_3325_, v___x_3330_, v_hist_3331_);
v_start_3334_ = lean_ctor_get(v_fst_3326_, 1);
v_stop_3335_ = lean_ctor_get(v_fst_3326_, 2);
v___x_3336_ = lean_nat_sub(v_stop_3335_, v_start_3334_);
v___x_3337_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3336_, v___x_3336_, v_fst_3326_, v___x_3332_, v___x_3330_, v___x_3333_);
lean_dec(v___x_3332_);
lean_dec(v___x_3336_);
v_buckets_3338_ = lean_ctor_get(v___x_3337_, 1);
lean_inc_ref(v_buckets_3338_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = lean_box(0);
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_array_get_size(v_buckets_3338_);
v___x_3369_ = lean_nat_dec_lt(v___x_3330_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_dec_ref(v_buckets_3338_);
v___y_3341_ = v___x_3367_;
goto v___jp_3340_;
}
else
{
size_t v___x_3370_; size_t v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = lean_usize_of_nat(v___x_3368_);
v___x_3371_ = ((size_t)0ULL);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3338_, v___x_3370_, v___x_3371_, v___x_3367_);
lean_dec_ref(v_buckets_3338_);
v___y_3341_ = v___x_3372_;
goto v___jp_3340_;
}
v___jp_3340_:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3341_, v___x_3339_);
lean_dec(v___y_3341_);
if (lean_obj_tag(v___x_3342_) == 1)
{
lean_object* v_val_3343_; lean_object* v_snd_3344_; lean_object* v_snd_3345_; lean_object* v_fst_3346_; lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v___x_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3352_; lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_val_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref(v___x_3342_);
v_snd_3344_ = lean_ctor_get(v_val_3343_, 1);
lean_inc(v_snd_3344_);
lean_dec(v_val_3343_);
v_snd_3345_ = lean_ctor_get(v_snd_3344_, 1);
lean_inc(v_snd_3345_);
v_fst_3346_ = lean_ctor_get(v_snd_3344_, 0);
lean_inc(v_fst_3346_);
lean_dec(v_snd_3344_);
v_fst_3347_ = lean_ctor_get(v_snd_3345_, 0);
lean_inc(v_fst_3347_);
v_snd_3348_ = lean_ctor_get(v_snd_3345_, 1);
lean_inc(v_snd_3348_);
lean_dec(v_snd_3345_);
v___x_3349_ = l_Subarray_split___redArg(v_fst_3325_, v_fst_3347_);
lean_dec(v_fst_3347_);
v_fst_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v___x_3349_, 1);
lean_inc(v_snd_3351_);
lean_dec_ref(v___x_3349_);
v___x_3352_ = l_Subarray_split___redArg(v_fst_3326_, v_snd_3348_);
lean_dec(v_snd_3348_);
v_fst_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_fst_3353_);
v_snd_3354_ = lean_ctor_get(v___x_3352_, 1);
lean_inc(v_snd_3354_);
lean_dec_ref(v___x_3352_);
v___x_3355_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3350_, v_fst_3353_);
v___x_3356_ = l_Array_append___redArg(v_fst_3320_, v___x_3355_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = lean_unsigned_to_nat(1u);
v___x_3358_ = lean_mk_empty_array_with_capacity(v___x_3357_);
v___x_3359_ = lean_array_push(v___x_3358_, v_fst_3346_);
v___x_3360_ = l_Array_append___redArg(v___x_3356_, v___x_3359_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = l_Subarray_drop___redArg(v_snd_3351_, v___x_3357_);
v___x_3362_ = l_Subarray_drop___redArg(v_snd_3354_, v___x_3357_);
v___x_3363_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3361_, v___x_3362_);
v___x_3364_ = l_Array_append___redArg(v___x_3360_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = l_Array_append___redArg(v___x_3364_, v_snd_3327_);
lean_dec(v_snd_3327_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; 
lean_dec(v___x_3342_);
lean_dec(v_fst_3326_);
lean_dec(v_fst_3325_);
v___x_3366_ = l_Array_append___redArg(v_fst_3320_, v_snd_3327_);
lean_dec(v_snd_3327_);
return v___x_3366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3373_, lean_object* v_original_3374_, lean_object* v_b_3375_){
_start:
{
lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3396_; 
v_fst_3376_ = lean_ctor_get(v_b_3375_, 0);
v_snd_3377_ = lean_ctor_get(v_b_3375_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_b_3375_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3379_ = v_b_3375_;
v_isShared_3380_ = v_isSharedCheck_3396_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_inc(v_fst_3376_);
lean_dec(v_b_3375_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3396_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
uint8_t v___x_3381_; 
v___x_3381_ = lean_nat_dec_lt(v_snd_3377_, v___x_3373_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3383_; 
if (v_isShared_3380_ == 0)
{
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_fst_3376_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_snd_3377_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
else
{
uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3385_ = 1;
v___x_3386_ = lean_array_fget_borrowed(v_original_3374_, v_snd_3377_);
v___x_3387_ = lean_box(v___x_3385_);
lean_inc(v___x_3386_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v___x_3386_);
lean_ctor_set(v___x_3379_, 0, v___x_3387_);
v___x_3389_ = v___x_3379_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3386_);
v___x_3389_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_array_push(v_fst_3376_, v___x_3389_);
v___x_3391_ = lean_unsigned_to_nat(1u);
v___x_3392_ = lean_nat_add(v_snd_3377_, v___x_3391_);
lean_dec(v_snd_3377_);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3390_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v_b_3375_ = v___x_3393_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3397_, lean_object* v_original_3398_, lean_object* v_b_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3397_, v_original_3398_, v_b_3399_);
lean_dec_ref(v_original_3398_);
lean_dec(v___x_3397_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3401_, size_t v_i_3402_, lean_object* v_bs_3403_){
_start:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_usize_dec_lt(v_i_3402_, v_sz_3401_);
if (v___x_3404_ == 0)
{
return v_bs_3403_;
}
else
{
lean_object* v_v_3405_; lean_object* v___x_3406_; lean_object* v_bs_x27_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; size_t v___x_3411_; size_t v___x_3412_; lean_object* v___x_3413_; 
v_v_3405_ = lean_array_uget(v_bs_3403_, v_i_3402_);
v___x_3406_ = lean_unsigned_to_nat(0u);
v_bs_x27_3407_ = lean_array_uset(v_bs_3403_, v_i_3402_, v___x_3406_);
v___x_3408_ = 0;
v___x_3409_ = lean_box(v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v_v_3405_);
v___x_3411_ = ((size_t)1ULL);
v___x_3412_ = lean_usize_add(v_i_3402_, v___x_3411_);
v___x_3413_ = lean_array_uset(v_bs_x27_3407_, v_i_3402_, v___x_3410_);
v_i_3402_ = v___x_3412_;
v_bs_3403_ = v___x_3413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3415_, lean_object* v_i_3416_, lean_object* v_bs_3417_){
_start:
{
size_t v_sz_boxed_3418_; size_t v_i_boxed_3419_; lean_object* v_res_3420_; 
v_sz_boxed_3418_ = lean_unbox_usize(v_sz_3415_);
lean_dec(v_sz_3415_);
v_i_boxed_3419_ = lean_unbox_usize(v_i_3416_);
lean_dec(v_i_3416_);
v_res_3420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3418_, v_i_boxed_3419_, v_bs_3417_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3421_, size_t v_i_3422_, lean_object* v_bs_3423_){
_start:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_usize_dec_lt(v_i_3422_, v_sz_3421_);
if (v___x_3424_ == 0)
{
return v_bs_3423_;
}
else
{
lean_object* v_v_3425_; lean_object* v___x_3426_; lean_object* v_bs_x27_3427_; uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v_v_3425_ = lean_array_uget(v_bs_3423_, v_i_3422_);
v___x_3426_ = lean_unsigned_to_nat(0u);
v_bs_x27_3427_ = lean_array_uset(v_bs_3423_, v_i_3422_, v___x_3426_);
v___x_3428_ = 1;
v___x_3429_ = lean_box(v___x_3428_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
lean_ctor_set(v___x_3430_, 1, v_v_3425_);
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3422_, v___x_3431_);
v___x_3433_ = lean_array_uset(v_bs_x27_3427_, v_i_3422_, v___x_3430_);
v_i_3422_ = v___x_3432_;
v_bs_3423_ = v___x_3433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3435_, lean_object* v_i_3436_, lean_object* v_bs_3437_){
_start:
{
size_t v_sz_boxed_3438_; size_t v_i_boxed_3439_; lean_object* v_res_3440_; 
v_sz_boxed_3438_ = lean_unbox_usize(v_sz_3435_);
lean_dec(v_sz_3435_);
v_i_boxed_3439_ = lean_unbox_usize(v_i_3436_);
lean_dec(v_i_3436_);
v_res_3440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3438_, v_i_boxed_3439_, v_bs_3437_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3448_, lean_object* v_edited_3449_){
_start:
{
lean_object* v_i_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v_i_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_array_get_size(v_original_3448_);
v___x_3452_ = lean_nat_dec_lt(v_i_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
size_t v_sz_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref(v_original_3448_);
v_sz_3453_ = lean_array_size(v_edited_3449_);
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3453_, v___x_3454_, v_edited_3449_);
return v___x_3455_;
}
else
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = lean_array_get_size(v_edited_3449_);
v___x_3457_ = lean_nat_dec_lt(v_i_3450_, v___x_3456_);
if (v___x_3457_ == 0)
{
size_t v_sz_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
lean_dec_ref(v_edited_3449_);
v_sz_3458_ = lean_array_size(v_original_3448_);
v___x_3459_ = ((size_t)0ULL);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3458_, v___x_3459_, v_original_3448_);
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v_ds_3463_; lean_object* v___x_3464_; size_t v_sz_3465_; size_t v___x_3466_; lean_object* v___x_3467_; lean_object* v_snd_3468_; lean_object* v_fst_3469_; lean_object* v_fst_3470_; lean_object* v_snd_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3490_; 
lean_inc_ref(v_original_3448_);
v___x_3461_ = l_Array_toSubarray___redArg(v_original_3448_, v_i_3450_, v___x_3451_);
lean_inc_ref(v_edited_3449_);
v___x_3462_ = l_Array_toSubarray___redArg(v_edited_3449_, v_i_3450_, v___x_3456_);
v_ds_3463_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3461_, v___x_3462_);
v___x_3464_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3465_ = lean_array_size(v_ds_3463_);
v___x_3466_ = ((size_t)0ULL);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3449_, v___x_3456_, v_original_3448_, v___x_3451_, v_ds_3463_, v_sz_3465_, v___x_3466_, v___x_3464_);
lean_dec_ref(v_ds_3463_);
v_snd_3468_ = lean_ctor_get(v___x_3467_, 1);
lean_inc(v_snd_3468_);
v_fst_3469_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_fst_3469_);
lean_dec_ref(v___x_3467_);
v_fst_3470_ = lean_ctor_get(v_snd_3468_, 0);
v_snd_3471_ = lean_ctor_get(v_snd_3468_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_snd_3468_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3473_ = v_snd_3468_;
v_isShared_3474_ = v_isSharedCheck_3490_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_snd_3471_);
lean_inc(v_fst_3470_);
lean_dec(v_snd_3468_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3490_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 1, v_fst_3470_);
lean_ctor_set(v___x_3473_, 0, v_fst_3469_);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3469_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_fst_3470_);
v___x_3476_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v_fst_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3487_; 
v___x_3477_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3451_, v_original_3448_, v___x_3476_);
lean_dec_ref(v_original_3448_);
v_fst_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v___x_3477_, 1);
lean_dec(v_unused_3488_);
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_fst_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 1, v_snd_3471_);
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_fst_3478_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_snd_3471_);
v___x_3483_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3484_; lean_object* v_fst_3485_; 
v___x_3484_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3456_, v_edited_3449_, v___x_3483_);
lean_dec_ref(v_edited_3449_);
v_fst_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_fst_3485_);
lean_dec_ref(v___x_3484_);
return v_fst_3485_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3491_, lean_object* v_x_3492_, lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3492_) == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = l_List_reverse___redArg(v_x_3493_);
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
return v___x_3496_;
}
else
{
lean_object* v_head_3497_; lean_object* v_tail_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3507_; 
v_head_3497_ = lean_ctor_get(v_x_3492_, 0);
v_tail_3498_ = lean_ctor_get(v_x_3492_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_x_3492_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3500_ = v_x_3492_;
v_isShared_3501_ = v_isSharedCheck_3507_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_tail_3498_);
lean_inc(v_head_3497_);
lean_dec(v_x_3492_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3507_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3497_, v___y_3491_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_x_3493_);
lean_ctor_set(v___x_3500_, 0, v___x_3502_);
v___x_3504_ = v___x_3500_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_x_3493_);
v___x_3504_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
v_x_3492_ = v_tail_3498_;
v_x_3493_ = v___x_3504_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3508_, lean_object* v_x_3509_, lean_object* v_x_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3508_, v_x_3509_, v_x_3510_);
lean_dec(v___y_3508_);
return v_res_3512_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = l_Lean_MessageLog_empty;
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; uint8_t v___y_3574_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; uint8_t v___y_3641_; lean_object* v___y_3642_; uint8_t v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_dc_x3f_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3529_);
v___x_3778_ = l_Lean_Syntax_isOfKind(v_x_3529_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; 
lean_dec(v_x_3529_);
v___x_3779_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3779_;
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3780_ = lean_unsigned_to_nat(0u);
v___x_3781_ = l_Lean_Syntax_getArg(v_x_3529_, v___x_3780_);
v___x_3782_ = l_Lean_Syntax_isNone(v___x_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3783_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3781_);
v___x_3784_ = l_Lean_Syntax_matchesNull(v___x_3781_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec(v___x_3781_);
lean_dec(v_x_3529_);
v___x_3785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3785_;
}
else
{
lean_object* v_dc_x3f_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v_dc_x3f_3786_ = l_Lean_Syntax_getArg(v___x_3781_, v___x_3780_);
lean_dec(v___x_3781_);
v___x_3787_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3786_);
v___x_3788_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec(v_dc_x3f_3786_);
lean_dec(v_x_3529_);
v___x_3789_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3789_;
}
else
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v_dc_x3f_3786_);
v_dc_x3f_3758_ = v___x_3790_;
v___y_3759_ = v_a_3530_;
v___y_3760_ = v_a_3531_;
goto v___jp_3757_;
}
}
}
else
{
lean_object* v___x_3791_; 
lean_dec(v___x_3781_);
v___x_3791_ = lean_box(0);
v_dc_x3f_3758_ = v___x_3791_;
v___y_3759_ = v_a_3530_;
v___y_3760_ = v_a_3531_;
goto v___jp_3757_;
}
}
v___jp_3533_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3539_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3540_ = l_Lean_stringToMessageData(v___y_3538_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3537_, v___x_3541_, v___y_3534_, v___y_3536_);
lean_dec(v___y_3537_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3563_; 
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; 
v_unused_3564_ = lean_ctor_get(v___x_3542_, 0);
lean_dec(v_unused_3564_);
v___x_3544_ = v___x_3542_;
v_isShared_3545_ = v_isSharedCheck_3563_;
goto v_resetjp_3543_;
}
else
{
lean_dec(v___x_3542_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3563_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Elab_Command_getRef___redArg(v___y_3534_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___y_3535_);
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v_a_3547_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 10);
lean_ctor_set(v___x_3544_, 0, v___x_3550_);
v___x_3552_ = v___x_3544_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3552_, v___y_3534_, v___y_3536_);
return v___x_3553_;
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_del_object(v___x_3544_);
lean_dec_ref(v___y_3535_);
v_a_3555_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3546_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3546_);
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
}
else
{
lean_dec_ref(v___y_3535_);
return v___x_3542_;
}
}
v___jp_3565_:
{
if (v___y_3574_ == 0)
{
lean_object* v___x_3575_; lean_object* v_env_3576_; lean_object* v_scopes_3577_; lean_object* v_usedQuotCtxts_3578_; lean_object* v_nextMacroScope_3579_; lean_object* v_maxRecDepth_3580_; lean_object* v_ngen_3581_; lean_object* v_auxDeclNGen_3582_; lean_object* v_infoState_3583_; lean_object* v_traceState_3584_; lean_object* v_snapshotTasks_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v___y_3566_);
v___x_3575_ = lean_st_ref_take(v___y_3571_);
v_env_3576_ = lean_ctor_get(v___x_3575_, 0);
v_scopes_3577_ = lean_ctor_get(v___x_3575_, 2);
v_usedQuotCtxts_3578_ = lean_ctor_get(v___x_3575_, 3);
v_nextMacroScope_3579_ = lean_ctor_get(v___x_3575_, 4);
v_maxRecDepth_3580_ = lean_ctor_get(v___x_3575_, 5);
v_ngen_3581_ = lean_ctor_get(v___x_3575_, 6);
v_auxDeclNGen_3582_ = lean_ctor_get(v___x_3575_, 7);
v_infoState_3583_ = lean_ctor_get(v___x_3575_, 8);
v_traceState_3584_ = lean_ctor_get(v___x_3575_, 9);
v_snapshotTasks_3585_ = lean_ctor_get(v___x_3575_, 10);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v___x_3575_, 1);
lean_dec(v_unused_3612_);
v___x_3587_ = v___x_3575_;
v_isShared_3588_ = v_isSharedCheck_3611_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snapshotTasks_3585_);
lean_inc(v_traceState_3584_);
lean_inc(v_infoState_3583_);
lean_inc(v_auxDeclNGen_3582_);
lean_inc(v_ngen_3581_);
lean_inc(v_maxRecDepth_3580_);
lean_inc(v_nextMacroScope_3579_);
lean_inc(v_usedQuotCtxts_3578_);
lean_inc(v_scopes_3577_);
lean_inc(v_env_3576_);
lean_dec(v___x_3575_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3611_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v___y_3573_);
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_env_3576_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v___y_3573_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_scopes_3577_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_usedQuotCtxts_3578_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_nextMacroScope_3579_);
lean_ctor_set(v_reuseFailAlloc_3610_, 5, v_maxRecDepth_3580_);
lean_ctor_set(v_reuseFailAlloc_3610_, 6, v_ngen_3581_);
lean_ctor_set(v_reuseFailAlloc_3610_, 7, v_auxDeclNGen_3582_);
lean_ctor_set(v_reuseFailAlloc_3610_, 8, v_infoState_3583_);
lean_ctor_set(v_reuseFailAlloc_3610_, 9, v_traceState_3584_);
lean_ctor_set(v_reuseFailAlloc_3610_, 10, v_snapshotTasks_3585_);
v___x_3590_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_scopes_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v_opts_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3591_ = lean_st_ref_set(v___y_3571_, v___x_3590_);
v___x_3592_ = lean_st_ref_get(v___y_3571_);
v_scopes_3593_ = lean_ctor_get(v___x_3592_, 2);
lean_inc(v_scopes_3593_);
lean_dec(v___x_3592_);
v___x_3594_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3595_ = l_List_head_x21___redArg(v___x_3594_, v_scopes_3593_);
lean_dec(v_scopes_3593_);
v_opts_3596_ = lean_ctor_get(v___x_3595_, 1);
lean_inc_ref(v_opts_3596_);
lean_dec(v___x_3595_);
v___x_3597_ = l_guard__msgs_diff;
v___x_3598_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3596_, v___x_3597_);
lean_dec_ref(v_opts_3596_);
if (v___x_3598_ == 0)
{
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_inc_ref(v___y_3568_);
v___y_3534_ = v___y_3567_;
v___y_3535_ = v___y_3568_;
v___y_3536_ = v___y_3571_;
v___y_3537_ = v___y_3572_;
v___y_3538_ = v___y_3568_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3599_ = lean_string_utf8_byte_size(v___y_3569_);
lean_inc(v___y_3570_);
lean_inc_ref(v___y_3569_);
v___x_3600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___y_3569_);
lean_ctor_set(v___x_3600_, 1, v___y_3570_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
v___x_3601_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3600_);
v___x_3602_ = lean_mk_empty_array_with_capacity(v___y_3570_);
lean_inc_ref(v___x_3602_);
v___x_3603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3569_, v___x_3600_, v___x_3599_, v___x_3601_, v___x_3602_);
lean_dec_ref(v___x_3600_);
v___x_3604_ = lean_string_utf8_byte_size(v___y_3568_);
lean_inc_ref_n(v___y_3568_, 2);
v___x_3605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3605_, 0, v___y_3568_);
lean_ctor_set(v___x_3605_, 1, v___y_3570_);
lean_ctor_set(v___x_3605_, 2, v___x_3604_);
v___x_3606_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3605_);
v___x_3607_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3568_, v___x_3605_, v___x_3604_, v___x_3606_, v___x_3602_);
lean_dec_ref(v___x_3605_);
v___x_3608_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3603_, v___x_3607_);
v___x_3609_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3608_);
lean_dec_ref(v___x_3608_);
v___y_3534_ = v___y_3567_;
v___y_3535_ = v___y_3568_;
v___y_3536_ = v___y_3571_;
v___y_3537_ = v___y_3572_;
v___y_3538_ = v___x_3609_;
goto v___jp_3533_;
}
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v_env_3614_; lean_object* v_scopes_3615_; lean_object* v_usedQuotCtxts_3616_; lean_object* v_nextMacroScope_3617_; lean_object* v_maxRecDepth_3618_; lean_object* v_ngen_3619_; lean_object* v_auxDeclNGen_3620_; lean_object* v_infoState_3621_; lean_object* v_traceState_3622_; lean_object* v_snapshotTasks_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3633_; 
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
v___x_3613_ = lean_st_ref_take(v___y_3571_);
v_env_3614_ = lean_ctor_get(v___x_3613_, 0);
v_scopes_3615_ = lean_ctor_get(v___x_3613_, 2);
v_usedQuotCtxts_3616_ = lean_ctor_get(v___x_3613_, 3);
v_nextMacroScope_3617_ = lean_ctor_get(v___x_3613_, 4);
v_maxRecDepth_3618_ = lean_ctor_get(v___x_3613_, 5);
v_ngen_3619_ = lean_ctor_get(v___x_3613_, 6);
v_auxDeclNGen_3620_ = lean_ctor_get(v___x_3613_, 7);
v_infoState_3621_ = lean_ctor_get(v___x_3613_, 8);
v_traceState_3622_ = lean_ctor_get(v___x_3613_, 9);
v_snapshotTasks_3623_ = lean_ctor_get(v___x_3613_, 10);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v___x_3613_, 1);
lean_dec(v_unused_3634_);
v___x_3625_ = v___x_3613_;
v_isShared_3626_ = v_isSharedCheck_3633_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_snapshotTasks_3623_);
lean_inc(v_traceState_3622_);
lean_inc(v_infoState_3621_);
lean_inc(v_auxDeclNGen_3620_);
lean_inc(v_ngen_3619_);
lean_inc(v_maxRecDepth_3618_);
lean_inc(v_nextMacroScope_3617_);
lean_inc(v_usedQuotCtxts_3616_);
lean_inc(v_scopes_3615_);
lean_inc(v_env_3614_);
lean_dec(v___x_3613_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3633_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 1, v___y_3566_);
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_env_3614_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___y_3566_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_scopes_3615_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_usedQuotCtxts_3616_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v_nextMacroScope_3617_);
lean_ctor_set(v_reuseFailAlloc_3632_, 5, v_maxRecDepth_3618_);
lean_ctor_set(v_reuseFailAlloc_3632_, 6, v_ngen_3619_);
lean_ctor_set(v_reuseFailAlloc_3632_, 7, v_auxDeclNGen_3620_);
lean_ctor_set(v_reuseFailAlloc_3632_, 8, v_infoState_3621_);
lean_ctor_set(v_reuseFailAlloc_3632_, 9, v_traceState_3622_);
lean_ctor_set(v_reuseFailAlloc_3632_, 10, v_snapshotTasks_3623_);
v___x_3628_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_st_ref_set(v___y_3571_, v___x_3628_);
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
}
}
v___jp_3635_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v_str_3658_; lean_object* v_startInclusive_3659_; lean_object* v_endExclusive_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3675_; 
v___x_3648_ = l_Lean_MessageLog_toList(v___y_3642_);
lean_dec(v___y_3642_);
v___x_3649_ = lean_box(0);
v___x_3650_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3647_, v___x_3648_, v___x_3649_);
lean_dec(v___y_3647_);
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3643_, v_a_3651_);
v___x_3653_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3654_ = l_String_intercalate(v___x_3653_, v___x_3652_);
v___x_3655_ = lean_string_utf8_byte_size(v___x_3654_);
lean_inc(v___y_3640_);
v___x_3656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___y_3640_);
lean_ctor_set(v___x_3656_, 2, v___x_3655_);
v___x_3657_ = l_String_Slice_trimAscii(v___x_3656_);
v_str_3658_ = lean_ctor_get(v___x_3657_, 0);
v_startInclusive_3659_ = lean_ctor_get(v___x_3657_, 1);
v_endExclusive_3660_ = lean_ctor_get(v___x_3657_, 2);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3662_ = v___x_3657_;
v_isShared_3663_ = v_isSharedCheck_3675_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_endExclusive_3660_);
lean_inc(v_startInclusive_3659_);
lean_inc(v_str_3658_);
lean_dec(v___x_3657_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3675_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_string_utf8_extract(v_str_3658_, v_startInclusive_3659_, v_endExclusive_3660_);
lean_dec(v_endExclusive_3660_);
lean_dec(v_startInclusive_3659_);
lean_dec_ref(v_str_3658_);
if (v___y_3641_ == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
lean_del_object(v___x_3662_);
lean_inc_ref(v___y_3639_);
v___x_3665_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___y_3639_);
lean_inc_ref(v___x_3664_);
v___x_3666_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___x_3664_);
v___x_3667_ = lean_string_dec_eq(v___x_3665_, v___x_3666_);
lean_dec_ref(v___x_3666_);
lean_dec_ref(v___x_3665_);
v___y_3566_ = v___y_3636_;
v___y_3567_ = v___y_3637_;
v___y_3568_ = v___x_3664_;
v___y_3569_ = v___y_3639_;
v___y_3570_ = v___y_3640_;
v___y_3571_ = v___y_3644_;
v___y_3572_ = v___y_3646_;
v___y_3573_ = v___y_3645_;
v___y_3574_ = v___x_3667_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
lean_inc_ref(v___x_3664_);
v___x_3668_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___x_3664_);
lean_inc_ref(v___y_3639_);
v___x_3669_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___y_3639_);
v___x_3670_ = lean_string_utf8_byte_size(v___x_3668_);
lean_inc(v___y_3640_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 2, v___x_3670_);
lean_ctor_set(v___x_3662_, 1, v___y_3640_);
lean_ctor_set(v___x_3662_, 0, v___x_3668_);
v___x_3672_ = v___x_3662_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___y_3640_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
uint8_t v___x_3673_; 
v___x_3673_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3669_, v___x_3672_);
lean_dec_ref(v___x_3672_);
v___y_3566_ = v___y_3636_;
v___y_3567_ = v___y_3637_;
v___y_3568_ = v___x_3664_;
v___y_3569_ = v___y_3639_;
v___y_3570_ = v___y_3640_;
v___y_3571_ = v___y_3644_;
v___y_3572_ = v___y_3646_;
v___y_3573_ = v___y_3645_;
v___y_3574_ = v___x_3673_;
goto v___jp_3565_;
}
}
}
}
v___jp_3676_:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3678_, v___y_3677_, v___y_3680_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v_filterFn_3685_; uint8_t v_whitespace_3686_; uint8_t v_ordering_3687_; uint8_t v_reportPositions_3688_; uint8_t v_substring_3689_; lean_object* v___x_3690_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref(v___x_3683_);
v_filterFn_3685_ = lean_ctor_get(v_a_3684_, 0);
lean_inc_ref(v_filterFn_3685_);
v_whitespace_3686_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*1);
v_ordering_3687_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*1 + 1);
v_reportPositions_3688_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*1 + 2);
v_substring_3689_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*1 + 3);
lean_dec(v_a_3684_);
v___x_3690_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3679_, v___y_3677_, v___y_3680_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v_a_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v_str_3700_; lean_object* v_startInclusive_3701_; lean_object* v_endExclusive_3702_; lean_object* v_fst_3703_; lean_object* v_snd_3704_; lean_object* v_fileMap_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = l_Lean_MessageLog_toList(v_a_3691_);
v___x_3693_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3694_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3685_, v___x_3692_, v___x_3693_);
lean_dec(v___x_3692_);
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
v___x_3696_ = lean_unsigned_to_nat(0u);
v___x_3697_ = lean_string_utf8_byte_size(v___y_3682_);
v___x_3698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3698_, 0, v___y_3682_);
lean_ctor_set(v___x_3698_, 1, v___x_3696_);
lean_ctor_set(v___x_3698_, 2, v___x_3697_);
v___x_3699_ = l_String_Slice_trimAscii(v___x_3698_);
v_str_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc_ref(v_str_3700_);
v_startInclusive_3701_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_startInclusive_3701_);
v_endExclusive_3702_ = lean_ctor_get(v___x_3699_, 2);
lean_inc(v_endExclusive_3702_);
lean_dec_ref(v___x_3699_);
v_fst_3703_ = lean_ctor_get(v_a_3695_, 0);
lean_inc(v_fst_3703_);
v_snd_3704_ = lean_ctor_get(v_a_3695_, 1);
lean_inc(v_snd_3704_);
lean_dec(v_a_3695_);
v_fileMap_3705_ = lean_ctor_get(v___y_3677_, 1);
v___x_3706_ = lean_string_utf8_extract(v_str_3700_, v_startInclusive_3701_, v_endExclusive_3702_);
lean_dec(v_endExclusive_3702_);
lean_dec(v_startInclusive_3701_);
lean_dec_ref(v_str_3700_);
v___x_3707_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3706_);
if (v_reportPositions_3688_ == 0)
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_box(0);
v___y_3636_ = v_snd_3704_;
v___y_3637_ = v___y_3677_;
v___y_3638_ = v_whitespace_3686_;
v___y_3639_ = v___x_3707_;
v___y_3640_ = v___x_3696_;
v___y_3641_ = v_substring_3689_;
v___y_3642_ = v_fst_3703_;
v___y_3643_ = v_ordering_3687_;
v___y_3644_ = v___y_3680_;
v___y_3645_ = v_a_3691_;
v___y_3646_ = v___y_3681_;
v___y_3647_ = v___x_3708_;
goto v___jp_3635_;
}
else
{
uint8_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = 0;
v___x_3710_ = l_Lean_Syntax_getPos_x3f(v___y_3681_, v___x_3709_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_box(0);
v___y_3636_ = v_snd_3704_;
v___y_3637_ = v___y_3677_;
v___y_3638_ = v_whitespace_3686_;
v___y_3639_ = v___x_3707_;
v___y_3640_ = v___x_3696_;
v___y_3641_ = v_substring_3689_;
v___y_3642_ = v_fst_3703_;
v___y_3643_ = v_ordering_3687_;
v___y_3644_ = v___y_3680_;
v___y_3645_ = v_a_3691_;
v___y_3646_ = v___y_3681_;
v___y_3647_ = v___x_3711_;
goto v___jp_3635_;
}
else
{
lean_object* v_val_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3721_; 
v_val_3712_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3714_ = v___x_3710_;
v_isShared_3715_ = v_isSharedCheck_3721_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_val_3712_);
lean_dec(v___x_3710_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3721_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v_line_3717_; lean_object* v___x_3719_; 
lean_inc_ref(v_fileMap_3705_);
v___x_3716_ = l_Lean_FileMap_toPosition(v_fileMap_3705_, v_val_3712_);
lean_dec(v_val_3712_);
v_line_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_line_3717_);
lean_dec_ref(v___x_3716_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v_line_3717_);
v___x_3719_ = v___x_3714_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_line_3717_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
v___y_3636_ = v_snd_3704_;
v___y_3637_ = v___y_3677_;
v___y_3638_ = v_whitespace_3686_;
v___y_3639_ = v___x_3707_;
v___y_3640_ = v___x_3696_;
v___y_3641_ = v_substring_3689_;
v___y_3642_ = v_fst_3703_;
v___y_3643_ = v_ordering_3687_;
v___y_3644_ = v___y_3680_;
v___y_3645_ = v_a_3691_;
v___y_3646_ = v___y_3681_;
v___y_3647_ = v___x_3719_;
goto v___jp_3635_;
}
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v_filterFn_3685_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
v_a_3722_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3690_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3690_);
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
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec(v___y_3679_);
v_a_3730_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3683_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3683_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
v___jp_3738_:
{
if (lean_obj_tag(v___y_3742_) == 0)
{
lean_object* v___x_3745_; 
v___x_3745_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3677_ = v___y_3739_;
v___y_3678_ = v___y_3744_;
v___y_3679_ = v___y_3740_;
v___y_3680_ = v___y_3741_;
v___y_3681_ = v___y_3743_;
v___y_3682_ = v___x_3745_;
goto v___jp_3676_;
}
else
{
lean_object* v_val_3746_; lean_object* v___x_3747_; 
v_val_3746_ = lean_ctor_get(v___y_3742_, 0);
lean_inc(v_val_3746_);
lean_dec_ref(v___y_3742_);
v___x_3747_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3746_, v___y_3739_, v___y_3741_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref(v___x_3747_);
v___y_3677_ = v___y_3739_;
v___y_3678_ = v___y_3744_;
v___y_3679_ = v___y_3740_;
v___y_3680_ = v___y_3741_;
v___y_3681_ = v___y_3743_;
v___y_3682_ = v_a_3748_;
goto v___jp_3676_;
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec(v___y_3740_);
v_a_3749_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3747_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3747_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
v___jp_3757_:
{
lean_object* v___x_3761_; lean_object* v_tk_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3761_ = lean_unsigned_to_nat(1u);
v_tk_3762_ = l_Lean_Syntax_getArg(v_x_3529_, v___x_3761_);
v___x_3763_ = lean_unsigned_to_nat(2u);
v___x_3764_ = l_Lean_Syntax_getArg(v_x_3529_, v___x_3763_);
v___x_3765_ = lean_unsigned_to_nat(4u);
v___x_3766_ = l_Lean_Syntax_getArg(v_x_3529_, v___x_3765_);
lean_dec(v_x_3529_);
v___x_3767_ = l_Lean_Syntax_getOptional_x3f(v___x_3764_);
lean_dec(v___x_3764_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_box(0);
v___y_3739_ = v___y_3759_;
v___y_3740_ = v___x_3766_;
v___y_3741_ = v___y_3760_;
v___y_3742_ = v_dc_x3f_3758_;
v___y_3743_ = v_tk_3762_;
v___y_3744_ = v___x_3768_;
goto v___jp_3738_;
}
else
{
lean_object* v_val_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
v_val_3769_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3767_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_val_3769_);
lean_dec(v___x_3767_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_val_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
v___y_3739_ = v___y_3759_;
v___y_3740_ = v___x_3766_;
v___y_3741_ = v___y_3760_;
v___y_3742_ = v_dc_x3f_3758_;
v___y_3743_ = v_tk_3762_;
v___y_3744_ = v___x_3774_;
goto v___jp_3738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3792_, v_a_3793_, v_a_3794_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3797_, lean_object* v_as_3798_, lean_object* v_as_x27_3799_, lean_object* v_b_3800_, lean_object* v_a_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3797_, v_as_x27_3799_, v_b_3800_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3806_, lean_object* v_as_3807_, lean_object* v_as_x27_3808_, lean_object* v_b_3809_, lean_object* v_a_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3806_, v_as_3807_, v_as_x27_3808_, v_b_3809_, v_a_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v_as_x27_3808_);
lean_dec(v_as_3807_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3815_, lean_object* v_x_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3815_, v_x_3816_, v_x_3817_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3822_, lean_object* v_x_3823_, lean_object* v_x_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3822_, v_x_3823_, v_x_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3822_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3829_, v___y_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v___x_3841_, lean_object* v_inst_3842_, lean_object* v_R_3843_, lean_object* v_a_3844_, lean_object* v_b_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3839_, v___x_3840_, v___x_3841_, v_a_3844_, v_b_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3847_, lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v_inst_3850_, lean_object* v_R_3851_, lean_object* v_a_3852_, lean_object* v_b_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3847_, v___x_3848_, v___x_3849_, v_inst_3850_, v_R_3851_, v_a_3852_, v_b_3853_);
lean_dec_ref(v___x_3848_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3855_, v___y_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3865_, lean_object* v___x_3866_, lean_object* v___x_3867_, lean_object* v_inst_3868_, lean_object* v_R_3869_, lean_object* v_a_3870_, lean_object* v_b_3871_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3865_, v___x_3866_, v___x_3867_, v_a_3870_, v_b_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v_inst_3876_, lean_object* v_R_3877_, lean_object* v_a_3878_, lean_object* v_b_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3873_, v___x_3874_, v___x_3875_, v_inst_3876_, v_R_3877_, v_a_3878_, v_b_3879_);
lean_dec_ref(v___x_3874_);
return v_res_3880_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3881_, lean_object* v_inst_3882_, lean_object* v_R_3883_, lean_object* v_a_3884_, uint8_t v_b_3885_, lean_object* v_c_3886_){
_start:
{
uint8_t v___x_3887_; 
v___x_3887_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3881_, v_a_3884_, v_b_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3888_, lean_object* v_inst_3889_, lean_object* v_R_3890_, lean_object* v_a_3891_, lean_object* v_b_3892_, lean_object* v_c_3893_){
_start:
{
uint8_t v_b_boxed_3894_; uint8_t v_res_3895_; lean_object* v_r_3896_; 
v_b_boxed_3894_ = lean_unbox(v_b_3892_);
v_res_3895_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3888_, v_inst_3889_, v_R_3890_, v_a_3891_, v_b_boxed_3894_, v_c_3893_);
lean_dec_ref(v_s_3888_);
v_r_3896_ = lean_box(v_res_3895_);
return v_r_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3897_, lean_object* v_ref_3898_, lean_object* v_msg_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3898_, v_msg_3899_, v___y_3900_, v___y_3901_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3904_, lean_object* v_ref_3905_, lean_object* v_msg_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3904_, v_ref_3905_, v_msg_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v_ref_3905_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3911_, lean_object* v_as_x27_3912_, lean_object* v_b_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3912_, v_b_3913_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3916_, lean_object* v_as_x27_3917_, lean_object* v_b_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3916_, v_as_x27_3917_, v_b_3918_, v_a_3919_);
lean_dec(v_as_x27_3917_);
lean_dec(v_as_3916_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3921_, lean_object* v_rsize_3922_, lean_object* v_histogram_3923_, lean_object* v_index_3924_, lean_object* v_val_3925_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3923_, v_index_3924_, v_val_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3927_, lean_object* v_rsize_3928_, lean_object* v_histogram_3929_, lean_object* v_index_3930_, lean_object* v_val_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3927_, v_rsize_3928_, v_histogram_3929_, v_index_3930_, v_val_3931_);
lean_dec(v_rsize_3928_);
lean_dec(v_lsize_3927_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3933_, lean_object* v___x_3934_, lean_object* v_fst_3935_, lean_object* v___x_3936_, lean_object* v_inst_3937_, lean_object* v_R_3938_, lean_object* v_a_3939_, lean_object* v_b_3940_, lean_object* v_c_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3933_, v___x_3934_, v_fst_3935_, v___x_3936_, v_a_3939_, v_b_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3943_, lean_object* v___x_3944_, lean_object* v_fst_3945_, lean_object* v___x_3946_, lean_object* v_inst_3947_, lean_object* v_R_3948_, lean_object* v_a_3949_, lean_object* v_b_3950_, lean_object* v_c_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3943_, v___x_3944_, v_fst_3945_, v___x_3946_, v_inst_3947_, v_R_3948_, v_a_3949_, v_b_3950_, v_c_3951_);
lean_dec(v___x_3946_);
lean_dec_ref(v_fst_3945_);
lean_dec(v___x_3944_);
lean_dec(v_upperBound_3943_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_3953_, lean_object* v_rsize_3954_, lean_object* v_histogram_3955_, lean_object* v_index_3956_, lean_object* v_val_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_3955_, v_index_3956_, v_val_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_3959_, lean_object* v_rsize_3960_, lean_object* v_histogram_3961_, lean_object* v_index_3962_, lean_object* v_val_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_3959_, v_rsize_3960_, v_histogram_3961_, v_index_3962_, v_val_3963_);
lean_dec(v_rsize_3960_);
lean_dec(v_lsize_3959_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_3965_, lean_object* v_fst_3966_, lean_object* v___x_3967_, lean_object* v_fst_3968_, lean_object* v_inst_3969_, lean_object* v_R_3970_, lean_object* v_a_3971_, lean_object* v_b_3972_, lean_object* v_c_3973_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3965_, v_fst_3966_, v___x_3967_, v_fst_3968_, v_a_3971_, v_b_3972_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_3975_, lean_object* v_fst_3976_, lean_object* v___x_3977_, lean_object* v_fst_3978_, lean_object* v_inst_3979_, lean_object* v_R_3980_, lean_object* v_a_3981_, lean_object* v_b_3982_, lean_object* v_c_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_3975_, v_fst_3976_, v___x_3977_, v_fst_3978_, v_inst_3979_, v_R_3980_, v_a_3981_, v_b_3982_, v_c_3983_);
lean_dec_ref(v_fst_3978_);
lean_dec(v___x_3977_);
lean_dec_ref(v_fst_3976_);
lean_dec(v_upperBound_3975_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_3985_, lean_object* v_msg_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_3986_, v___y_3987_, v___y_3988_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_3991_, lean_object* v_msg_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_3991_, v_msg_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_3997_, lean_object* v_m_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_3998_, v_a_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_4001_, lean_object* v_m_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_4001_, v_m_4002_, v_a_4003_);
lean_dec_ref(v_a_4003_);
lean_dec_ref(v_m_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_4005_, lean_object* v_m_4006_, lean_object* v_a_4007_, lean_object* v_b_4008_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_4006_, v_a_4007_, v_b_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4010_, lean_object* v_macroStack_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4010_, v_macroStack_4011_, v___y_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4016_, lean_object* v_macroStack_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4016_, v_macroStack_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4022_, lean_object* v_R_4023_, lean_object* v_a_4024_, lean_object* v_b_4025_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4024_, v_b_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4027_, lean_object* v_a_4028_, lean_object* v_x_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4028_, v_x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4031_, lean_object* v_a_4032_, lean_object* v_x_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4031_, v_a_4032_, v_x_4033_);
lean_dec(v_x_4033_);
lean_dec_ref(v_a_4032_);
return v_res_4034_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4035_, lean_object* v_a_4036_, lean_object* v_x_4037_){
_start:
{
uint8_t v___x_4038_; 
v___x_4038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4036_, v_x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4039_, lean_object* v_a_4040_, lean_object* v_x_4041_){
_start:
{
uint8_t v_res_4042_; lean_object* v_r_4043_; 
v_res_4042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4039_, v_a_4040_, v_x_4041_);
lean_dec(v_x_4041_);
lean_dec_ref(v_a_4040_);
v_r_4043_ = lean_box(v_res_4042_);
return v_r_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4044_, lean_object* v_data_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4047_, lean_object* v_a_4048_, lean_object* v_b_4049_, lean_object* v_x_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4048_, v_b_4049_, v_x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4052_, lean_object* v_i_4053_, lean_object* v_source_4054_, lean_object* v_target_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4053_, v_source_4054_, v_target_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4057_, lean_object* v_x_4058_, lean_object* v_x_4059_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4058_, v_x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4069_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4070_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4071_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4072_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4073_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4069_, v___x_4070_, v___x_4071_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4104_ = l_Lean_addBuiltinDeclarationRanges(v___x_4102_, v___x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4107_){
_start:
{
lean_object* v_doc_4109_; lean_object* v___x_4110_; 
v_doc_4109_ = lean_ctor_get(v___y_4107_, 1);
lean_inc_ref(v_doc_4109_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v_doc_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4111_);
lean_dec_ref(v___y_4111_);
return v_res_4113_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4114_, lean_object* v_a_4115_, uint8_t v_b_4116_){
_start:
{
lean_object* v_str_4117_; lean_object* v_startInclusive_4118_; lean_object* v_endExclusive_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
v_str_4117_ = lean_ctor_get(v_s_4114_, 0);
v_startInclusive_4118_ = lean_ctor_get(v_s_4114_, 1);
v_endExclusive_4119_ = lean_ctor_get(v_s_4114_, 2);
v___x_4120_ = lean_nat_sub(v_endExclusive_4119_, v_startInclusive_4118_);
v___x_4121_ = lean_nat_dec_eq(v_a_4115_, v___x_4120_);
lean_dec(v___x_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; uint32_t v___x_4123_; uint32_t v___x_4124_; uint8_t v___x_4125_; 
v___x_4122_ = lean_nat_add(v_startInclusive_4118_, v_a_4115_);
lean_dec(v_a_4115_);
v___x_4123_ = lean_string_utf8_get_fast(v_str_4117_, v___x_4122_);
v___x_4124_ = 10;
v___x_4125_ = lean_uint32_dec_eq(v___x_4123_, v___x_4124_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_string_utf8_next_fast(v_str_4117_, v___x_4122_);
lean_dec(v___x_4122_);
v___x_4127_ = lean_nat_sub(v___x_4126_, v_startInclusive_4118_);
v_a_4115_ = v___x_4127_;
v_b_4116_ = v___x_4125_;
goto _start;
}
else
{
lean_dec(v___x_4122_);
return v___x_4125_;
}
}
else
{
lean_dec(v_a_4115_);
return v_b_4116_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4129_, lean_object* v_a_4130_, lean_object* v_b_4131_){
_start:
{
uint8_t v_b_boxed_4132_; uint8_t v_res_4133_; lean_object* v_r_4134_; 
v_b_boxed_4132_ = lean_unbox(v_b_4131_);
v_res_4133_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4129_, v_a_4130_, v_b_boxed_4132_);
lean_dec_ref(v_s_4129_);
v_r_4134_ = lean_box(v_res_4133_);
return v_r_4134_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4135_){
_start:
{
lean_object* v_searcher_4136_; uint8_t v___x_4137_; uint8_t v___x_4138_; 
v_searcher_4136_ = lean_unsigned_to_nat(0u);
v___x_4137_ = 0;
v___x_4138_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4135_, v_searcher_4136_, v___x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4139_){
_start:
{
uint8_t v_res_4140_; lean_object* v_r_4141_; 
v_res_4140_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4139_);
lean_dec_ref(v_s_4139_);
v_r_4141_ = lean_box(v_res_4140_);
return v_r_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4153_, lean_object* v_fst_4154_, uint8_t v___x_4155_, lean_object* v_a_4156_, lean_object* v___x_4157_, lean_object* v___x_4158_, lean_object* v___x_4159_, lean_object* v___x_4160_, lean_object* v___x_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v_snd_4165_, lean_object* v___x_4166_){
_start:
{
if (lean_obj_tag(v___x_4153_) == 1)
{
lean_object* v_val_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4231_; 
v_val_4168_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4170_ = v___x_4153_;
v_isShared_4171_ = v_isSharedCheck_4231_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_val_4168_);
lean_dec(v___x_4153_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4231_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4174_ = l_Lean_Syntax_setArg(v_fst_4154_, v___x_4172_, v___x_4173_);
v___x_4175_ = l_Lean_Syntax_getPos_x3f(v___x_4174_, v___x_4155_);
lean_dec(v___x_4174_);
if (lean_obj_tag(v___x_4175_) == 1)
{
lean_object* v_val_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4227_; 
lean_dec_ref(v___x_4166_);
v_val_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4227_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_val_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4227_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___y_4181_; lean_object* v___x_4207_; uint8_t v___y_4214_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4207_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4165_);
v___x_4219_ = lean_string_utf8_byte_size(v___x_4207_);
v___x_4220_ = lean_nat_dec_eq(v___x_4219_, v___x_4172_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; uint8_t v___x_4223_; 
v___x_4221_ = lean_string_length(v___x_4207_);
v___x_4222_ = lean_unsigned_to_nat(93u);
v___x_4223_ = lean_nat_dec_le(v___x_4221_, v___x_4222_);
if (v___x_4223_ == 0)
{
v___y_4214_ = v___x_4223_;
goto v___jp_4213_;
}
else
{
lean_object* v___x_4224_; uint8_t v___x_4225_; 
lean_inc_ref(v___x_4207_);
v___x_4224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4207_);
lean_ctor_set(v___x_4224_, 1, v___x_4172_);
lean_ctor_set(v___x_4224_, 2, v___x_4219_);
v___x_4225_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4224_);
lean_dec_ref(v___x_4224_);
if (v___x_4225_ == 0)
{
v___y_4214_ = v___x_4223_;
goto v___jp_4213_;
}
else
{
goto v___jp_4208_;
}
}
}
else
{
lean_object* v___x_4226_; 
lean_dec_ref(v___x_4207_);
v___x_4226_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4181_ = v___x_4226_;
goto v___jp_4180_;
}
v___jp_4180_:
{
lean_object* v_toEditableDocumentCore_4182_; lean_object* v_meta_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4203_; 
v_toEditableDocumentCore_4182_ = lean_ctor_get(v_a_4156_, 0);
lean_inc_ref(v_toEditableDocumentCore_4182_);
v_meta_4183_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_toEditableDocumentCore_4182_);
if (v_isSharedCheck_4203_ == 0)
{
lean_object* v_unused_4204_; lean_object* v_unused_4205_; lean_object* v_unused_4206_; 
v_unused_4204_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 3);
lean_dec(v_unused_4204_);
v_unused_4205_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 2);
lean_dec(v_unused_4205_);
v_unused_4206_ = lean_ctor_get(v_toEditableDocumentCore_4182_, 1);
lean_dec(v_unused_4206_);
v___x_4185_ = v_toEditableDocumentCore_4182_;
v_isShared_4186_ = v_isSharedCheck_4203_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_meta_4183_);
lean_dec(v_toEditableDocumentCore_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4203_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v_text_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
v_text_4187_ = lean_ctor_get(v_meta_4183_, 3);
lean_inc_ref(v_text_4187_);
lean_dec_ref(v_meta_4183_);
v___x_4188_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4156_);
v___x_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4189_, 0, v_val_4168_);
lean_ctor_set(v___x_4189_, 1, v_val_4176_);
v___x_4190_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4187_, v___x_4189_);
v___x_4191_ = lean_box(0);
lean_inc(v___x_4157_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 3, v___x_4157_);
lean_ctor_set(v___x_4185_, 2, v___x_4191_);
lean_ctor_set(v___x_4185_, 1, v___y_4181_);
lean_ctor_set(v___x_4185_, 0, v___x_4190_);
v___x_4193_ = v___x_4185_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___y_4181_);
lean_ctor_set(v_reuseFailAlloc_4202_, 2, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4202_, 3, v___x_4157_);
v___x_4193_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
v___x_4194_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4188_, v___x_4193_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4194_);
v___x_4196_ = v___x_4178_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; lean_object* v___x_4199_; 
lean_inc(v___x_4157_);
v___x_4197_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4157_);
lean_ctor_set(v___x_4197_, 1, v___x_4157_);
lean_ctor_set(v___x_4197_, 2, v___x_4158_);
lean_ctor_set(v___x_4197_, 3, v___x_4159_);
lean_ctor_set(v___x_4197_, 4, v___x_4160_);
lean_ctor_set(v___x_4197_, 5, v___x_4161_);
lean_ctor_set(v___x_4197_, 6, v___x_4162_);
lean_ctor_set(v___x_4197_, 7, v___x_4196_);
lean_ctor_set(v___x_4197_, 8, v___x_4163_);
lean_ctor_set(v___x_4197_, 9, v___x_4164_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4197_);
v___x_4199_ = v___x_4170_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
v___jp_4208_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4209_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4210_ = lean_string_append(v___x_4209_, v___x_4207_);
lean_dec_ref(v___x_4207_);
v___x_4211_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4212_ = lean_string_append(v___x_4210_, v___x_4211_);
v___y_4181_ = v___x_4212_;
goto v___jp_4180_;
}
v___jp_4213_:
{
if (v___y_4214_ == 0)
{
goto v___jp_4208_;
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4215_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4216_ = lean_string_append(v___x_4215_, v___x_4207_);
lean_dec_ref(v___x_4207_);
v___x_4217_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4218_ = lean_string_append(v___x_4216_, v___x_4217_);
v___y_4181_ = v___x_4218_;
goto v___jp_4180_;
}
}
}
}
else
{
lean_object* v___x_4229_; 
lean_dec(v___x_4175_);
lean_dec(v_val_4168_);
lean_dec_ref(v_snd_4165_);
lean_dec(v___x_4164_);
lean_dec(v___x_4163_);
lean_dec(v___x_4162_);
lean_dec(v___x_4161_);
lean_dec(v___x_4160_);
lean_dec(v___x_4159_);
lean_dec_ref(v___x_4158_);
lean_dec(v___x_4157_);
lean_dec_ref(v_a_4156_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4166_);
v___x_4229_ = v___x_4170_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4166_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v___x_4232_; 
lean_dec_ref(v_snd_4165_);
lean_dec(v___x_4164_);
lean_dec(v___x_4163_);
lean_dec(v___x_4162_);
lean_dec(v___x_4161_);
lean_dec(v___x_4160_);
lean_dec(v___x_4159_);
lean_dec_ref(v___x_4158_);
lean_dec(v___x_4157_);
lean_dec_ref(v_a_4156_);
lean_dec(v_fst_4154_);
lean_dec(v___x_4153_);
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4166_);
return v___x_4232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4233_, lean_object* v_fst_4234_, lean_object* v___x_4235_, lean_object* v_a_4236_, lean_object* v___x_4237_, lean_object* v___x_4238_, lean_object* v___x_4239_, lean_object* v___x_4240_, lean_object* v___x_4241_, lean_object* v___x_4242_, lean_object* v___x_4243_, lean_object* v___x_4244_, lean_object* v_snd_4245_, lean_object* v___x_4246_, lean_object* v___y_4247_){
_start:
{
uint8_t v___x_4549__boxed_4248_; lean_object* v_res_4249_; 
v___x_4549__boxed_4248_ = lean_unbox(v___x_4235_);
v_res_4249_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4233_, v_fst_4234_, v___x_4549__boxed_4248_, v_a_4236_, v___x_4237_, v___x_4238_, v___x_4239_, v___x_4240_, v___x_4241_, v___x_4242_, v___x_4243_, v___x_4244_, v_snd_4245_, v___x_4246_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4253_, size_t v_sz_4254_, size_t v_i_4255_, lean_object* v_b_4256_){
_start:
{
lean_object* v_a_4258_; uint8_t v___x_4262_; 
v___x_4262_ = lean_usize_dec_lt(v_i_4255_, v_sz_4254_);
if (v___x_4262_ == 0)
{
lean_inc_ref(v_b_4256_);
return v_b_4256_;
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v_a_4265_; 
v___x_4263_ = lean_box(0);
v___x_4264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4265_ = lean_array_uget(v_as_4253_, v_i_4255_);
if (lean_obj_tag(v_a_4265_) == 1)
{
lean_object* v_i_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4300_; 
v_i_4266_ = lean_ctor_get(v_a_4265_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_a_4265_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; 
v_unused_4301_ = lean_ctor_get(v_a_4265_, 1);
lean_dec(v_unused_4301_);
v___x_4268_ = v_a_4265_;
v_isShared_4269_ = v_isSharedCheck_4300_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_i_4266_);
lean_dec(v_a_4265_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4300_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
if (lean_obj_tag(v_i_4266_) == 10)
{
lean_object* v_i_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4299_; 
v_i_4270_ = lean_ctor_get(v_i_4266_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_i_4266_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4272_ = v_i_4266_;
v_isShared_4273_ = v_isSharedCheck_4299_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_i_4270_);
lean_dec(v_i_4266_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4299_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v_stx_4274_; lean_object* v_value_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4298_; 
v_stx_4274_ = lean_ctor_get(v_i_4270_, 0);
v_value_4275_ = lean_ctor_get(v_i_4270_, 1);
v_isSharedCheck_4298_ = !lean_is_exclusive(v_i_4270_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4277_ = v_i_4270_;
v_isShared_4278_ = v_isSharedCheck_4298_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_value_4275_);
lean_inc(v_stx_4274_);
lean_dec(v_i_4270_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4298_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4280_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4275_, v___x_4279_);
lean_dec(v_value_4275_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_del_object(v___x_4277_);
lean_dec(v_stx_4274_);
lean_del_object(v___x_4272_);
lean_del_object(v___x_4268_);
v_a_4258_ = v___x_4264_;
goto v___jp_4257_;
}
else
{
lean_object* v_val_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4297_; 
v_val_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4297_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_val_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4297_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 1, v_val_4281_);
v___x_4286_ = v___x_4277_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_stx_4274_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_val_4281_);
v___x_4286_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4288_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4286_);
v___x_4288_ = v___x_4283_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4290_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set_tag(v___x_4272_, 1);
lean_ctor_set(v___x_4272_, 0, v___x_4288_);
v___x_4290_ = v___x_4272_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
lean_object* v___x_4292_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set_tag(v___x_4268_, 0);
lean_ctor_set(v___x_4268_, 1, v___x_4263_);
lean_ctor_set(v___x_4268_, 0, v___x_4290_);
v___x_4292_ = v___x_4268_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v___x_4263_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
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
lean_del_object(v___x_4268_);
lean_dec_ref(v_i_4266_);
v_a_4258_ = v___x_4264_;
goto v___jp_4257_;
}
}
}
else
{
lean_dec(v_a_4265_);
v_a_4258_ = v___x_4264_;
goto v___jp_4257_;
}
}
v___jp_4257_:
{
size_t v___x_4259_; size_t v___x_4260_; 
v___x_4259_ = ((size_t)1ULL);
v___x_4260_ = lean_usize_add(v_i_4255_, v___x_4259_);
v_i_4255_ = v___x_4260_;
v_b_4256_ = v_a_4258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4302_, lean_object* v_sz_4303_, lean_object* v_i_4304_, lean_object* v_b_4305_){
_start:
{
size_t v_sz_boxed_4306_; size_t v_i_boxed_4307_; lean_object* v_res_4308_; 
v_sz_boxed_4306_ = lean_unbox_usize(v_sz_4303_);
lean_dec(v_sz_4303_);
v_i_boxed_4307_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_res_4308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4302_, v_sz_boxed_4306_, v_i_boxed_4307_, v_b_4305_);
lean_dec_ref(v_b_4305_);
lean_dec_ref(v_as_4302_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4309_, size_t v_sz_4310_, size_t v_i_4311_, lean_object* v_b_4312_){
_start:
{
lean_object* v_a_4314_; uint8_t v___x_4318_; 
v___x_4318_ = lean_usize_dec_lt(v_i_4311_, v_sz_4310_);
if (v___x_4318_ == 0)
{
lean_inc_ref(v_b_4312_);
return v_b_4312_;
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v_a_4321_; 
v___x_4319_ = lean_box(0);
v___x_4320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4321_ = lean_array_uget(v_as_4309_, v_i_4311_);
if (lean_obj_tag(v_a_4321_) == 1)
{
lean_object* v_i_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4356_; 
v_i_4322_ = lean_ctor_get(v_a_4321_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_a_4321_);
if (v_isSharedCheck_4356_ == 0)
{
lean_object* v_unused_4357_; 
v_unused_4357_ = lean_ctor_get(v_a_4321_, 1);
lean_dec(v_unused_4357_);
v___x_4324_ = v_a_4321_;
v_isShared_4325_ = v_isSharedCheck_4356_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_i_4322_);
lean_dec(v_a_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4356_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
if (lean_obj_tag(v_i_4322_) == 10)
{
lean_object* v_i_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4355_; 
v_i_4326_ = lean_ctor_get(v_i_4322_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_i_4322_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4328_ = v_i_4322_;
v_isShared_4329_ = v_isSharedCheck_4355_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_i_4326_);
lean_dec(v_i_4322_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4355_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_stx_4330_; lean_object* v_value_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4354_; 
v_stx_4330_ = lean_ctor_get(v_i_4326_, 0);
v_value_4331_ = lean_ctor_get(v_i_4326_, 1);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_i_4326_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4333_ = v_i_4326_;
v_isShared_4334_ = v_isSharedCheck_4354_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_value_4331_);
lean_inc(v_stx_4330_);
lean_dec(v_i_4326_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4354_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4336_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4331_, v___x_4335_);
lean_dec(v_value_4331_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_del_object(v___x_4333_);
lean_dec(v_stx_4330_);
lean_del_object(v___x_4328_);
lean_del_object(v___x_4324_);
v_a_4314_ = v___x_4320_;
goto v___jp_4313_;
}
else
{
lean_object* v_val_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4353_; 
v_val_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4353_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_val_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4353_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 1, v_val_4337_);
v___x_4342_ = v___x_4333_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_stx_4330_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_val_4337_);
v___x_4342_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4344_; 
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4342_);
v___x_4344_ = v___x_4339_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4346_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 1);
lean_ctor_set(v___x_4328_, 0, v___x_4344_);
v___x_4346_ = v___x_4328_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4344_);
v___x_4346_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4348_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set_tag(v___x_4324_, 0);
lean_ctor_set(v___x_4324_, 1, v___x_4319_);
lean_ctor_set(v___x_4324_, 0, v___x_4346_);
v___x_4348_ = v___x_4324_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v___x_4319_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
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
lean_del_object(v___x_4324_);
lean_dec_ref(v_i_4322_);
v_a_4314_ = v___x_4320_;
goto v___jp_4313_;
}
}
}
else
{
lean_dec(v_a_4321_);
v_a_4314_ = v___x_4320_;
goto v___jp_4313_;
}
}
v___jp_4313_:
{
size_t v___x_4315_; size_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_add(v_i_4311_, v___x_4315_);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4309_, v_sz_4310_, v___x_4316_, v_a_4314_);
return v___x_4317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4358_, lean_object* v_sz_4359_, lean_object* v_i_4360_, lean_object* v_b_4361_){
_start:
{
size_t v_sz_boxed_4362_; size_t v_i_boxed_4363_; lean_object* v_res_4364_; 
v_sz_boxed_4362_ = lean_unbox_usize(v_sz_4359_);
lean_dec(v_sz_4359_);
v_i_boxed_4363_ = lean_unbox_usize(v_i_4360_);
lean_dec(v_i_4360_);
v_res_4364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4358_, v_sz_boxed_4362_, v_i_boxed_4363_, v_b_4361_);
lean_dec_ref(v_b_4361_);
lean_dec_ref(v_as_4358_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4365_){
_start:
{
if (lean_obj_tag(v_x_4365_) == 0)
{
lean_object* v_cs_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; size_t v_sz_4369_; size_t v___x_4370_; lean_object* v___x_4371_; lean_object* v_fst_4372_; 
v_cs_4366_ = lean_ctor_get(v_x_4365_, 0);
v___x_4367_ = lean_box(0);
v___x_4368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4369_ = lean_array_size(v_cs_4366_);
v___x_4370_ = ((size_t)0ULL);
v___x_4371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4366_, v_sz_4369_, v___x_4370_, v___x_4368_);
v_fst_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_fst_4372_);
lean_dec_ref(v___x_4371_);
if (lean_obj_tag(v_fst_4372_) == 0)
{
return v___x_4367_;
}
else
{
lean_object* v_val_4373_; 
v_val_4373_ = lean_ctor_get(v_fst_4372_, 0);
lean_inc(v_val_4373_);
lean_dec_ref(v_fst_4372_);
return v_val_4373_;
}
}
else
{
lean_object* v_vs_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; size_t v_sz_4377_; size_t v___x_4378_; lean_object* v___x_4379_; lean_object* v_fst_4380_; 
v_vs_4374_ = lean_ctor_get(v_x_4365_, 0);
v___x_4375_ = lean_box(0);
v___x_4376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4377_ = lean_array_size(v_vs_4374_);
v___x_4378_ = ((size_t)0ULL);
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4374_, v_sz_4377_, v___x_4378_, v___x_4376_);
v_fst_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_fst_4380_);
lean_dec_ref(v___x_4379_);
if (lean_obj_tag(v_fst_4380_) == 0)
{
return v___x_4375_;
}
else
{
lean_object* v_val_4381_; 
v_val_4381_ = lean_ctor_get(v_fst_4380_, 0);
lean_inc(v_val_4381_);
lean_dec_ref(v_fst_4380_);
return v_val_4381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4382_, size_t v_sz_4383_, size_t v_i_4384_, lean_object* v_b_4385_){
_start:
{
uint8_t v___x_4386_; 
v___x_4386_ = lean_usize_dec_lt(v_i_4384_, v_sz_4383_);
if (v___x_4386_ == 0)
{
lean_inc_ref(v_b_4385_);
return v_b_4385_;
}
else
{
lean_object* v___x_4387_; lean_object* v_a_4388_; lean_object* v___x_4389_; 
v___x_4387_ = lean_box(0);
v_a_4388_ = lean_array_uget_borrowed(v_as_4382_, v_i_4384_);
v___x_4389_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4388_);
if (lean_obj_tag(v___x_4389_) == 1)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
lean_ctor_set(v___x_4391_, 1, v___x_4387_);
return v___x_4391_;
}
else
{
lean_object* v___x_4392_; size_t v___x_4393_; size_t v___x_4394_; 
lean_dec(v___x_4389_);
v___x_4392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4393_ = ((size_t)1ULL);
v___x_4394_ = lean_usize_add(v_i_4384_, v___x_4393_);
v_i_4384_ = v___x_4394_;
v_b_4385_ = v___x_4392_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4396_, lean_object* v_sz_4397_, lean_object* v_i_4398_, lean_object* v_b_4399_){
_start:
{
size_t v_sz_boxed_4400_; size_t v_i_boxed_4401_; lean_object* v_res_4402_; 
v_sz_boxed_4400_ = lean_unbox_usize(v_sz_4397_);
lean_dec(v_sz_4397_);
v_i_boxed_4401_ = lean_unbox_usize(v_i_4398_);
lean_dec(v_i_4398_);
v_res_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4396_, v_sz_boxed_4400_, v_i_boxed_4401_, v_b_4399_);
lean_dec_ref(v_b_4399_);
lean_dec_ref(v_as_4396_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4403_);
lean_dec_ref(v_x_4403_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4405_){
_start:
{
lean_object* v_root_4406_; lean_object* v_tail_4407_; lean_object* v___x_4408_; 
v_root_4406_ = lean_ctor_get(v_t_4405_, 0);
v_tail_4407_ = lean_ctor_get(v_t_4405_, 1);
v___x_4408_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4406_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v___x_4409_; size_t v_sz_4410_; size_t v___x_4411_; lean_object* v___x_4412_; lean_object* v_fst_4413_; 
v___x_4409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4410_ = lean_array_size(v_tail_4407_);
v___x_4411_ = ((size_t)0ULL);
v___x_4412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4407_, v_sz_4410_, v___x_4411_, v___x_4409_);
v_fst_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_fst_4413_);
lean_dec_ref(v___x_4412_);
if (lean_obj_tag(v_fst_4413_) == 0)
{
return v___x_4408_;
}
else
{
lean_object* v_val_4414_; 
v_val_4414_ = lean_ctor_get(v_fst_4413_, 0);
lean_inc(v_val_4414_);
lean_dec_ref(v_fst_4413_);
return v_val_4414_;
}
}
else
{
return v___x_4408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4415_);
lean_dec_ref(v_t_4415_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4431_, lean_object* v_a_4432_){
_start:
{
if (lean_obj_tag(v_node_4431_) == 1)
{
lean_object* v_children_4434_; lean_object* v_res_4435_; 
v_children_4434_ = lean_ctor_get(v_node_4431_, 1);
v_res_4435_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4434_);
if (lean_obj_tag(v_res_4435_) == 1)
{
lean_object* v_val_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4473_; 
v_val_4436_ = lean_ctor_get(v_res_4435_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_res_4435_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4438_ = v_res_4435_;
v_isShared_4439_ = v_isSharedCheck_4473_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_val_4436_);
lean_dec(v_res_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4473_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v_fst_4440_; lean_object* v_snd_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4472_; 
v_fst_4440_ = lean_ctor_get(v_val_4436_, 0);
v_snd_4441_ = lean_ctor_get(v_val_4436_, 1);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_val_4436_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4443_ = v_val_4436_;
v_isShared_4444_ = v_isSharedCheck_4472_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_snd_4441_);
lean_inc(v_fst_4440_);
lean_dec(v_val_4436_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4472_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4445_; lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4471_; 
v___x_4445_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4432_);
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4471_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4471_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___y_4458_; lean_object* v___x_4460_; 
v___x_4450_ = lean_box(0);
v___x_4451_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4452_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4453_ = 1;
v___x_4454_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4455_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4456_ = l_Lean_Syntax_getPos_x3f(v_fst_4440_, v___x_4453_);
v___x_4457_ = lean_box(v___x_4453_);
v___y_4458_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4458_, 0, v___x_4456_);
lean_closure_set(v___y_4458_, 1, v_fst_4440_);
lean_closure_set(v___y_4458_, 2, v___x_4457_);
lean_closure_set(v___y_4458_, 3, v_a_4446_);
lean_closure_set(v___y_4458_, 4, v___x_4450_);
lean_closure_set(v___y_4458_, 5, v___x_4451_);
lean_closure_set(v___y_4458_, 6, v___x_4452_);
lean_closure_set(v___y_4458_, 7, v___x_4450_);
lean_closure_set(v___y_4458_, 8, v___x_4454_);
lean_closure_set(v___y_4458_, 9, v___x_4450_);
lean_closure_set(v___y_4458_, 10, v___x_4450_);
lean_closure_set(v___y_4458_, 11, v___x_4450_);
lean_closure_set(v___y_4458_, 12, v_snd_4441_);
lean_closure_set(v___y_4458_, 13, v___x_4455_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___y_4458_);
v___x_4460_ = v___x_4438_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___y_4458_);
v___x_4460_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
lean_object* v___x_4462_; 
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 1, v___x_4460_);
lean_ctor_set(v___x_4443_, 0, v___x_4455_);
v___x_4462_ = v___x_4443_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4463_ = lean_unsigned_to_nat(1u);
v___x_4464_ = lean_mk_empty_array_with_capacity(v___x_4463_);
v___x_4465_ = lean_array_push(v___x_4464_, v___x_4462_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4465_);
v___x_4467_ = v___x_4448_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec(v_res_4435_);
v___x_4474_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
return v___x_4475_;
}
}
else
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4478_, v_a_4479_);
lean_dec_ref(v_a_4479_);
lean_dec_ref(v_node_4478_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4482_, lean_object* v_x_4483_, lean_object* v_x_4484_, lean_object* v_node_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4485_, v_a_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4489_, lean_object* v_x_4490_, lean_object* v_x_4491_, lean_object* v_node_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4489_, v_x_4490_, v_x_4491_, v_node_4492_, v_a_4493_);
lean_dec_ref(v_a_4493_);
lean_dec_ref(v_node_4492_);
lean_dec_ref(v_x_4491_);
lean_dec_ref(v_x_4490_);
lean_dec_ref(v_x_4489_);
return v_res_4495_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4496_, lean_object* v_inst_4497_, lean_object* v_R_4498_, lean_object* v_a_4499_, uint8_t v_b_4500_, lean_object* v_c_4501_){
_start:
{
uint8_t v___x_4502_; 
v___x_4502_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4496_, v_a_4499_, v_b_4500_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4503_, lean_object* v_inst_4504_, lean_object* v_R_4505_, lean_object* v_a_4506_, lean_object* v_b_4507_, lean_object* v_c_4508_){
_start:
{
uint8_t v_b_boxed_4509_; uint8_t v_res_4510_; lean_object* v_r_4511_; 
v_b_boxed_4509_ = lean_unbox(v_b_4507_);
v_res_4510_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4503_, v_inst_4504_, v_R_4505_, v_a_4506_, v_b_boxed_4509_, v_c_4508_);
lean_dec_ref(v_s_4503_);
v_r_4511_ = lean_box(v_res_4510_);
return v_r_4511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_(){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_));
v___x_4518_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4519_ = l_Lean_CodeAction_insertBuiltin(v___x_4517_, v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369____boxed(lean_object* v_a_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
return v_res_4521_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4524_ = lean_string_utf8_byte_size(v___x_4523_);
return v___x_4524_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4525_ = lean_unsigned_to_nat(0u);
v___x_4526_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4527_ = lean_nat_dec_eq(v___x_4526_, v___x_4525_);
return v___x_4527_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4528_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4529_ = lean_unsigned_to_nat(0u);
v___x_4530_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
lean_ctor_set(v___x_4531_, 1, v___x_4529_);
lean_ctor_set(v___x_4531_, 2, v___x_4528_);
return v___x_4531_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4533_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4532_);
return v___x_4533_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4536_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4537_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
lean_ctor_set(v___x_4537_, 1, v___x_4535_);
lean_ctor_set(v___x_4537_, 2, v___x_4534_);
lean_ctor_set(v___x_4537_, 3, v___x_4534_);
return v___x_4537_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4538_){
_start:
{
lean_object* v___y_4540_; uint8_t v___x_4543_; 
v___x_4543_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; 
v___x_4544_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4540_ = v___x_4544_;
goto v___jp_4539_;
}
else
{
lean_object* v___x_4545_; 
v___x_4545_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4540_ = v___x_4545_;
goto v___jp_4539_;
}
v___jp_4539_:
{
uint8_t v___x_4541_; uint8_t v___x_4542_; 
v___x_4541_ = 0;
lean_inc(v___y_4540_);
v___x_4542_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4538_, v___y_4540_, v___x_4541_);
return v___x_4542_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4546_){
_start:
{
uint8_t v_res_4547_; lean_object* v_r_4548_; 
v_res_4547_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4546_);
lean_dec_ref(v_s_4546_);
v_r_4548_ = lean_box(v_res_4547_);
return v_r_4548_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4549_, lean_object* v_as_x27_4550_, uint8_t v_b_4551_){
_start:
{
if (lean_obj_tag(v_as_x27_4550_) == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = lean_box(v_b_4551_);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
return v___x_4554_;
}
else
{
lean_object* v_head_4555_; uint8_t v_isSilent_4556_; 
v_head_4555_ = lean_ctor_get(v_as_x27_4550_, 0);
v_isSilent_4556_ = lean_ctor_get_uint8(v_head_4555_, sizeof(void*)*5 + 2);
if (v_isSilent_4556_ == 0)
{
lean_object* v_tail_4557_; lean_object* v_data_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_tail_4557_ = lean_ctor_get(v_as_x27_4550_, 1);
v_data_4558_ = lean_ctor_get(v_head_4555_, 4);
lean_inc(v_data_4558_);
v___x_4559_ = l_Lean_MessageData_toString(v_data_4558_);
v___x_4560_ = lean_unsigned_to_nat(0u);
v___x_4561_ = lean_string_utf8_byte_size(v___x_4559_);
v___x_4562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4559_);
lean_ctor_set(v___x_4562_, 1, v___x_4560_);
lean_ctor_set(v___x_4562_, 2, v___x_4561_);
v___x_4563_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4562_);
lean_dec_ref(v___x_4562_);
if (v___x_4563_ == 0)
{
v_as_x27_4550_ = v_tail_4557_;
goto _start;
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_box(v_foundPanic_4549_);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
}
else
{
lean_object* v_tail_4567_; 
v_tail_4567_ = lean_ctor_get(v_as_x27_4550_, 1);
v_as_x27_4550_ = v_tail_4567_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4569_, lean_object* v_as_x27_4570_, lean_object* v_b_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v_foundPanic_boxed_4573_; uint8_t v_b_boxed_4574_; lean_object* v_res_4575_; 
v_foundPanic_boxed_4573_ = lean_unbox(v_foundPanic_4569_);
v_b_boxed_4574_ = lean_unbox(v_b_4571_);
v_res_4575_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4573_, v_as_x27_4570_, v_b_boxed_4574_);
lean_dec(v_as_x27_4570_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4576_, uint8_t v_severity_4577_, uint8_t v_isSilent_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l_Lean_Elab_Command_getRef___redArg(v___y_4579_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4584_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref(v___x_4582_);
v___x_4584_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4583_, v_msgData_4576_, v_severity_4577_, v_isSilent_4578_, v___y_4579_, v___y_4580_);
lean_dec(v_a_4583_);
return v___x_4584_;
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_msgData_4576_);
v_a_4585_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4582_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4582_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4593_, lean_object* v_severity_4594_, lean_object* v_isSilent_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
uint8_t v_severity_boxed_4599_; uint8_t v_isSilent_boxed_4600_; lean_object* v_res_4601_; 
v_severity_boxed_4599_ = lean_unbox(v_severity_4594_);
v_isSilent_boxed_4600_ = lean_unbox(v_isSilent_4595_);
v_res_4601_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4593_, v_severity_boxed_4599_, v_isSilent_boxed_4600_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
uint8_t v___x_4606_; uint8_t v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = 2;
v___x_4607_ = 0;
v___x_4608_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4602_, v___x_4606_, v___x_4607_, v___y_4603_, v___y_4604_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
return v_res_4613_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4622_ = l_Lean_MessageData_ofFormat(v___x_4621_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v___x_4627_; uint8_t v_foundPanic_4628_; 
v___x_4627_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4623_);
v_foundPanic_4628_ = l_Lean_Syntax_isOfKind(v_x_4623_, v___x_4627_);
if (v_foundPanic_4628_ == 0)
{
lean_object* v___x_4629_; 
lean_dec(v_x_4623_);
v___x_4629_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4629_;
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = lean_unsigned_to_nat(2u);
v___x_4631_ = l_Lean_Syntax_getArg(v_x_4623_, v___x_4630_);
lean_dec(v_x_4623_);
v___x_4632_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4631_, v_a_4624_, v_a_4625_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4689_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref(v___x_4632_);
v___x_4634_ = 0;
v___x_4635_ = l_Lean_MessageLog_toList(v_a_4633_);
v___x_4636_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4628_, v___x_4635_, v___x_4634_);
lean_dec(v___x_4635_);
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4689_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4689_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
uint8_t v___x_4641_; 
v___x_4641_ = lean_unbox(v_a_4637_);
lean_dec(v_a_4637_);
if (v___x_4641_ == 0)
{
lean_object* v___x_4642_; lean_object* v_env_4643_; lean_object* v_scopes_4644_; lean_object* v_usedQuotCtxts_4645_; lean_object* v_nextMacroScope_4646_; lean_object* v_maxRecDepth_4647_; lean_object* v_ngen_4648_; lean_object* v_auxDeclNGen_4649_; lean_object* v_infoState_4650_; lean_object* v_traceState_4651_; lean_object* v_snapshotTasks_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4662_; 
lean_del_object(v___x_4639_);
v___x_4642_ = lean_st_ref_take(v_a_4625_);
v_env_4643_ = lean_ctor_get(v___x_4642_, 0);
v_scopes_4644_ = lean_ctor_get(v___x_4642_, 2);
v_usedQuotCtxts_4645_ = lean_ctor_get(v___x_4642_, 3);
v_nextMacroScope_4646_ = lean_ctor_get(v___x_4642_, 4);
v_maxRecDepth_4647_ = lean_ctor_get(v___x_4642_, 5);
v_ngen_4648_ = lean_ctor_get(v___x_4642_, 6);
v_auxDeclNGen_4649_ = lean_ctor_get(v___x_4642_, 7);
v_infoState_4650_ = lean_ctor_get(v___x_4642_, 8);
v_traceState_4651_ = lean_ctor_get(v___x_4642_, 9);
v_snapshotTasks_4652_ = lean_ctor_get(v___x_4642_, 10);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4662_ == 0)
{
lean_object* v_unused_4663_; 
v_unused_4663_ = lean_ctor_get(v___x_4642_, 1);
lean_dec(v_unused_4663_);
v___x_4654_ = v___x_4642_;
v_isShared_4655_ = v_isSharedCheck_4662_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_snapshotTasks_4652_);
lean_inc(v_traceState_4651_);
lean_inc(v_infoState_4650_);
lean_inc(v_auxDeclNGen_4649_);
lean_inc(v_ngen_4648_);
lean_inc(v_maxRecDepth_4647_);
lean_inc(v_nextMacroScope_4646_);
lean_inc(v_usedQuotCtxts_4645_);
lean_inc(v_scopes_4644_);
lean_inc(v_env_4643_);
lean_dec(v___x_4642_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4662_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 1, v_a_4633_);
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_env_4643_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v_a_4633_);
lean_ctor_set(v_reuseFailAlloc_4661_, 2, v_scopes_4644_);
lean_ctor_set(v_reuseFailAlloc_4661_, 3, v_usedQuotCtxts_4645_);
lean_ctor_set(v_reuseFailAlloc_4661_, 4, v_nextMacroScope_4646_);
lean_ctor_set(v_reuseFailAlloc_4661_, 5, v_maxRecDepth_4647_);
lean_ctor_set(v_reuseFailAlloc_4661_, 6, v_ngen_4648_);
lean_ctor_set(v_reuseFailAlloc_4661_, 7, v_auxDeclNGen_4649_);
lean_ctor_set(v_reuseFailAlloc_4661_, 8, v_infoState_4650_);
lean_ctor_set(v_reuseFailAlloc_4661_, 9, v_traceState_4651_);
lean_ctor_set(v_reuseFailAlloc_4661_, 10, v_snapshotTasks_4652_);
v___x_4657_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = lean_st_ref_set(v_a_4625_, v___x_4657_);
v___x_4659_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4660_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4659_, v_a_4624_, v_a_4625_);
return v___x_4660_;
}
}
}
else
{
lean_object* v___x_4664_; lean_object* v_env_4665_; lean_object* v_scopes_4666_; lean_object* v_usedQuotCtxts_4667_; lean_object* v_nextMacroScope_4668_; lean_object* v_maxRecDepth_4669_; lean_object* v_ngen_4670_; lean_object* v_auxDeclNGen_4671_; lean_object* v_infoState_4672_; lean_object* v_traceState_4673_; lean_object* v_snapshotTasks_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4687_; 
lean_dec(v_a_4633_);
v___x_4664_ = lean_st_ref_take(v_a_4625_);
v_env_4665_ = lean_ctor_get(v___x_4664_, 0);
v_scopes_4666_ = lean_ctor_get(v___x_4664_, 2);
v_usedQuotCtxts_4667_ = lean_ctor_get(v___x_4664_, 3);
v_nextMacroScope_4668_ = lean_ctor_get(v___x_4664_, 4);
v_maxRecDepth_4669_ = lean_ctor_get(v___x_4664_, 5);
v_ngen_4670_ = lean_ctor_get(v___x_4664_, 6);
v_auxDeclNGen_4671_ = lean_ctor_get(v___x_4664_, 7);
v_infoState_4672_ = lean_ctor_get(v___x_4664_, 8);
v_traceState_4673_ = lean_ctor_get(v___x_4664_, 9);
v_snapshotTasks_4674_ = lean_ctor_get(v___x_4664_, 10);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4687_ == 0)
{
lean_object* v_unused_4688_; 
v_unused_4688_ = lean_ctor_get(v___x_4664_, 1);
lean_dec(v_unused_4688_);
v___x_4676_ = v___x_4664_;
v_isShared_4677_ = v_isSharedCheck_4687_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_snapshotTasks_4674_);
lean_inc(v_traceState_4673_);
lean_inc(v_infoState_4672_);
lean_inc(v_auxDeclNGen_4671_);
lean_inc(v_ngen_4670_);
lean_inc(v_maxRecDepth_4669_);
lean_inc(v_nextMacroScope_4668_);
lean_inc(v_usedQuotCtxts_4667_);
lean_inc(v_scopes_4666_);
lean_inc(v_env_4665_);
lean_dec(v___x_4664_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4687_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4680_; 
v___x_4678_ = l_Lean_MessageLog_empty;
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 1, v___x_4678_);
v___x_4680_ = v___x_4676_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_env_4665_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_scopes_4666_);
lean_ctor_set(v_reuseFailAlloc_4686_, 3, v_usedQuotCtxts_4667_);
lean_ctor_set(v_reuseFailAlloc_4686_, 4, v_nextMacroScope_4668_);
lean_ctor_set(v_reuseFailAlloc_4686_, 5, v_maxRecDepth_4669_);
lean_ctor_set(v_reuseFailAlloc_4686_, 6, v_ngen_4670_);
lean_ctor_set(v_reuseFailAlloc_4686_, 7, v_auxDeclNGen_4671_);
lean_ctor_set(v_reuseFailAlloc_4686_, 8, v_infoState_4672_);
lean_ctor_set(v_reuseFailAlloc_4686_, 9, v_traceState_4673_);
lean_ctor_set(v_reuseFailAlloc_4686_, 10, v_snapshotTasks_4674_);
v___x_4680_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4681_ = lean_st_ref_set(v_a_4625_, v___x_4680_);
v___x_4682_ = lean_box(0);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4682_);
v___x_4684_ = v___x_4639_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
v_a_4690_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4632_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4632_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4698_, v_a_4699_, v_a_4700_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4703_, lean_object* v_as_4704_, lean_object* v_as_x27_4705_, uint8_t v_b_4706_, lean_object* v_a_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4703_, v_as_x27_4705_, v_b_4706_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4712_, lean_object* v_as_4713_, lean_object* v_as_x27_4714_, lean_object* v_b_4715_, lean_object* v_a_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
uint8_t v_foundPanic_boxed_4720_; uint8_t v_b_boxed_4721_; lean_object* v_res_4722_; 
v_foundPanic_boxed_4720_ = lean_unbox(v_foundPanic_4712_);
v_b_boxed_4721_ = lean_unbox(v_b_4715_);
v_res_4722_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4720_, v_as_4713_, v_as_x27_4714_, v_b_boxed_4721_, v_a_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v_as_x27_4714_);
lean_dec(v_as_4713_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4731_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4732_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4733_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4734_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4735_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4731_, v___x_4732_, v___x_4733_, v___x_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4737_;
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
res = l___private_Lean_Elab_GuardMsgs_0__initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_guard__msgs_diff = lean_io_result_get_value(res);
lean_mark_persistent(l_guard__msgs_diff);
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
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
