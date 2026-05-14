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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365____boxed(lean_object*);
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
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1824_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1823_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1823_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_messages_1782_; lean_object* v___y_1784_; lean_object* v_snapshotTasks_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1780_ = lean_st_ref_get(v_a_1762_);
v___x_1781_ = lean_st_ref_get(v_a_1762_);
v_messages_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc_ref(v_messages_1782_);
lean_dec(v___x_1780_);
v_snapshotTasks_1811_ = lean_ctor_get(v___x_1781_, 10);
lean_inc_ref(v_snapshotTasks_1811_);
lean_dec(v___x_1781_);
v___x_1812_ = l_Lean_MessageLog_empty;
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_size(v_snapshotTasks_1811_);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1784_ = v___x_1812_;
goto v___jp_1783_;
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_le(v___x_1814_, v___x_1814_);
if (v___x_1816_ == 0)
{
if (v___x_1815_ == 0)
{
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1784_ = v___x_1812_;
goto v___jp_1783_;
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1814_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1811_, v___x_1817_, v___x_1818_, v___x_1812_);
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1784_ = v___x_1819_;
goto v___jp_1783_;
}
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1814_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1811_, v___x_1820_, v___x_1821_, v___x_1812_);
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1784_ = v___x_1822_;
goto v___jp_1783_;
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v_env_1786_; lean_object* v_messages_1787_; lean_object* v_scopes_1788_; lean_object* v_usedQuotCtxts_1789_; lean_object* v_nextMacroScope_1790_; lean_object* v_maxRecDepth_1791_; lean_object* v_ngen_1792_; lean_object* v_auxDeclNGen_1793_; lean_object* v_infoState_1794_; lean_object* v_traceState_1795_; lean_object* v_newDecls_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1809_; 
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
v_newDecls_1796_ = lean_ctor_get(v___x_1785_, 11);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1785_, 10);
lean_dec(v_unused_1810_);
v___x_1798_ = v___x_1785_;
v_isShared_1799_ = v_isSharedCheck_1809_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_newDecls_1796_);
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
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1809_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 10, v___x_1800_);
v___x_1802_ = v___x_1798_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_env_1786_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_messages_1787_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_scopes_1788_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_usedQuotCtxts_1789_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_nextMacroScope_1790_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_maxRecDepth_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_ngen_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_auxDeclNGen_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_infoState_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1808_, 11, v_newDecls_1796_);
v___x_1802_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = lean_st_ref_set(v_a_1762_, v___x_1802_);
v___x_1804_ = l_Lean_MessageLog_append(v_messages_1782_, v___y_1784_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1804_);
v___x_1806_ = v___x_1778_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1776_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1776_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1837_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1838_, lean_object* v_opt_1839_){
_start:
{
lean_object* v_name_1840_; lean_object* v_defValue_1841_; lean_object* v_map_1842_; lean_object* v___x_1843_; 
v_name_1840_ = lean_ctor_get(v_opt_1839_, 0);
v_defValue_1841_ = lean_ctor_get(v_opt_1839_, 1);
v_map_1842_ = lean_ctor_get(v_opts_1838_, 0);
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1842_, v_name_1840_);
if (lean_obj_tag(v___x_1843_) == 0)
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_unbox(v_defValue_1841_);
return v___x_1844_;
}
else
{
lean_object* v_val_1845_; 
v_val_1845_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_val_1845_);
lean_dec_ref(v___x_1843_);
if (lean_obj_tag(v_val_1845_) == 1)
{
uint8_t v_v_1846_; 
v_v_1846_ = lean_ctor_get_uint8(v_val_1845_, 0);
lean_dec_ref(v_val_1845_);
return v_v_1846_;
}
else
{
uint8_t v___x_1847_; 
lean_dec(v_val_1845_);
v___x_1847_ = lean_unbox(v_defValue_1841_);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1848_, lean_object* v_opt_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1848_, v_opt_1849_);
lean_dec_ref(v_opt_1849_);
lean_dec_ref(v_opts_1848_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1856_);
lean_dec_ref(v_s_1856_);
return v_res_1857_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_box(1);
v___x_1859_ = l_Lean_MessageData_ofFormat(v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1864_ = l_Lean_MessageData_ofFormat(v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
return v_x_1865_;
}
else
{
lean_object* v_head_1867_; lean_object* v_tail_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1890_; 
v_head_1867_ = lean_ctor_get(v_x_1866_, 0);
v_tail_1868_ = lean_ctor_get(v_x_1866_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_x_1866_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1870_ = v_x_1866_;
v_isShared_1871_ = v_isSharedCheck_1890_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_tail_1868_);
lean_inc(v_head_1867_);
lean_dec(v_x_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1890_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_before_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1888_; 
v_before_1872_ = lean_ctor_get(v_head_1867_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_head_1867_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v_head_1867_, 1);
lean_dec(v_unused_1889_);
v___x_1874_ = v_head_1867_;
v_isShared_1875_ = v_isSharedCheck_1888_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_before_1872_);
lean_dec(v_head_1867_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1888_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 7);
lean_ctor_set(v___x_1874_, 1, v___x_1876_);
lean_ctor_set(v___x_1874_, 0, v_x_1865_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_x_1865_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 7);
lean_ctor_set(v___x_1870_, 1, v___x_1879_);
lean_ctor_set(v___x_1870_, 0, v___x_1878_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = l_Lean_MessageData_ofSyntax(v_before_1872_);
v___x_1883_ = l_Lean_indentD(v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v_x_1865_ = v___x_1884_;
v_x_1866_ = v_tail_1868_;
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
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1895_ = l_Lean_MessageData_ofFormat(v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1896_, lean_object* v_macroStack_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_scopes_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_opts_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1900_ = lean_st_ref_get(v___y_1898_);
v_scopes_1901_ = lean_ctor_get(v___x_1900_, 2);
lean_inc(v_scopes_1901_);
lean_dec(v___x_1900_);
v___x_1902_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1903_ = l_List_head_x21___redArg(v___x_1902_, v_scopes_1901_);
lean_dec(v_scopes_1901_);
v_opts_1904_ = lean_ctor_get(v___x_1903_, 1);
lean_inc_ref(v_opts_1904_);
lean_dec(v___x_1903_);
v___x_1905_ = l_Lean_Elab_pp_macroStack;
v___x_1906_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1904_, v___x_1905_);
lean_dec_ref(v_opts_1904_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_dec(v_macroStack_1897_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_msgData_1896_);
return v___x_1907_;
}
else
{
if (lean_obj_tag(v_macroStack_1897_) == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_msgData_1896_);
return v___x_1908_;
}
else
{
lean_object* v_head_1909_; lean_object* v_after_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1925_; 
v_head_1909_ = lean_ctor_get(v_macroStack_1897_, 0);
lean_inc(v_head_1909_);
v_after_1910_ = lean_ctor_get(v_head_1909_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_head_1909_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v_head_1909_, 0);
lean_dec(v_unused_1926_);
v___x_1912_ = v_head_1909_;
v_isShared_1913_ = v_isSharedCheck_1925_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_after_1910_);
lean_dec(v_head_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1925_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 7);
lean_ctor_set(v___x_1912_, 1, v___x_1914_);
lean_ctor_set(v___x_1912_, 0, v_msgData_1896_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_msgData_1896_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_msgData_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1917_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_MessageData_ofSyntax(v_after_1910_);
v___x_1920_ = l_Lean_indentD(v___x_1919_);
v_msgData_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1921_, 0, v___x_1918_);
lean_ctor_set(v_msgData_1921_, 1, v___x_1920_);
v___x_1922_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1921_, v_macroStack_1897_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1927_, lean_object* v_macroStack_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1927_, v_macroStack_1928_, v___y_1929_);
lean_dec(v___y_1929_);
return v_res_1931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
lean_ctor_set(v___x_1937_, 3, v___x_1936_);
lean_ctor_set(v___x_1937_, 4, v___x_1935_);
lean_ctor_set(v___x_1937_, 5, v___x_1935_);
lean_ctor_set(v___x_1937_, 6, v___x_1935_);
lean_ctor_set(v___x_1937_, 7, v___x_1935_);
lean_ctor_set(v___x_1937_, 8, v___x_1935_);
lean_ctor_set(v___x_1937_, 9, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_unsigned_to_nat(32u);
v___x_1939_ = lean_mk_empty_array_with_capacity(v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1941_ = ((size_t)5ULL);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_unsigned_to_nat(32u);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
v___x_1945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1946_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1944_);
lean_ctor_set(v___x_1946_, 2, v___x_1942_);
lean_ctor_set(v___x_1946_, 3, v___x_1942_);
lean_ctor_set_usize(v___x_1946_, 4, v___x_1941_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1947_ = lean_box(1);
v___x_1948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1949_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1948_);
lean_ctor_set(v___x_1950_, 2, v___x_1947_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v_env_1955_; lean_object* v___x_1956_; lean_object* v_scopes_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v_opts_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1954_ = lean_st_ref_get(v___y_1952_);
v_env_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc_ref(v_env_1955_);
lean_dec(v___x_1954_);
v___x_1956_ = lean_st_ref_get(v___y_1952_);
v_scopes_1957_ = lean_ctor_get(v___x_1956_, 2);
lean_inc(v_scopes_1957_);
lean_dec(v___x_1956_);
v___x_1958_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1959_ = l_List_head_x21___redArg(v___x_1958_, v_scopes_1957_);
lean_dec(v_scopes_1957_);
v_opts_1960_ = lean_ctor_get(v___x_1959_, 1);
lean_inc_ref(v_opts_1960_);
lean_dec(v___x_1959_);
v___x_1961_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1962_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1963_, 0, v_env_1955_);
lean_ctor_set(v___x_1963_, 1, v___x_1961_);
lean_ctor_set(v___x_1963_, 2, v___x_1962_);
lean_ctor_set(v___x_1963_, 3, v_opts_1960_);
v___x_1964_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_msgData_1951_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1966_, v___y_1967_);
lean_dec(v___y_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Elab_Command_getRef___redArg(v___y_1971_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v_macroStack_1976_; lean_object* v___x_1977_; lean_object* v_a_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1989_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
v_macroStack_1976_ = lean_ctor_get(v___y_1971_, 4);
v___x_1977_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1970_, v___y_1972_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
v___x_1979_ = l_Lean_Elab_getBetterRef(v_a_1975_, v_macroStack_1976_);
lean_dec(v_a_1975_);
lean_inc(v_macroStack_1976_);
v___x_1980_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1978_, v_macroStack_1976_, v___y_1972_);
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1979_);
lean_ctor_set(v___x_1985_, 1, v_a_1981_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 1);
lean_ctor_set(v___x_1983_, 0, v___x_1985_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v_msg_1970_);
v_a_1990_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1974_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1974_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_2003_, lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Elab_Command_getRef___redArg(v___y_2005_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v_fileName_2010_; lean_object* v_fileMap_2011_; lean_object* v_currRecDepth_2012_; lean_object* v_cmdPos_2013_; lean_object* v_macroStack_2014_; lean_object* v_quotContext_x3f_2015_; lean_object* v_currMacroScope_2016_; lean_object* v_snap_x3f_2017_; lean_object* v_cancelTk_x3f_2018_; uint8_t v_suppressElabErrors_2019_; lean_object* v_ref_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2008_);
v_fileName_2010_ = lean_ctor_get(v___y_2005_, 0);
v_fileMap_2011_ = lean_ctor_get(v___y_2005_, 1);
v_currRecDepth_2012_ = lean_ctor_get(v___y_2005_, 2);
v_cmdPos_2013_ = lean_ctor_get(v___y_2005_, 3);
v_macroStack_2014_ = lean_ctor_get(v___y_2005_, 4);
v_quotContext_x3f_2015_ = lean_ctor_get(v___y_2005_, 5);
v_currMacroScope_2016_ = lean_ctor_get(v___y_2005_, 6);
v_snap_x3f_2017_ = lean_ctor_get(v___y_2005_, 8);
v_cancelTk_x3f_2018_ = lean_ctor_get(v___y_2005_, 9);
v_suppressElabErrors_2019_ = lean_ctor_get_uint8(v___y_2005_, sizeof(void*)*10);
v_ref_2020_ = l_Lean_replaceRef(v_ref_2003_, v_a_2009_);
lean_dec(v_a_2009_);
lean_inc(v_cancelTk_x3f_2018_);
lean_inc(v_snap_x3f_2017_);
lean_inc(v_currMacroScope_2016_);
lean_inc(v_quotContext_x3f_2015_);
lean_inc(v_macroStack_2014_);
lean_inc(v_cmdPos_2013_);
lean_inc(v_currRecDepth_2012_);
lean_inc_ref(v_fileMap_2011_);
lean_inc_ref(v_fileName_2010_);
v___x_2021_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2021_, 0, v_fileName_2010_);
lean_ctor_set(v___x_2021_, 1, v_fileMap_2011_);
lean_ctor_set(v___x_2021_, 2, v_currRecDepth_2012_);
lean_ctor_set(v___x_2021_, 3, v_cmdPos_2013_);
lean_ctor_set(v___x_2021_, 4, v_macroStack_2014_);
lean_ctor_set(v___x_2021_, 5, v_quotContext_x3f_2015_);
lean_ctor_set(v___x_2021_, 6, v_currMacroScope_2016_);
lean_ctor_set(v___x_2021_, 7, v_ref_2020_);
lean_ctor_set(v___x_2021_, 8, v_snap_x3f_2017_);
lean_ctor_set(v___x_2021_, 9, v_cancelTk_x3f_2018_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*10, v_suppressElabErrors_2019_);
v___x_2022_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_2004_, v___x_2021_, v___y_2006_);
lean_dec_ref(v___x_2021_);
return v___x_2022_;
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_msg_2004_);
v_a_2023_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2008_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2008_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2031_, lean_object* v_msg_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2031_, v_msg_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v_ref_2031_);
return v_res_2036_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_val_2054_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_unsigned_to_nat(1u);
v___x_2062_ = l_Lean_Syntax_getArg(v_stx_2043_, v___x_2061_);
switch(lean_obj_tag(v___x_2062_))
{
case 2:
{
lean_object* v_val_2063_; 
lean_dec(v_stx_2043_);
v_val_2063_ = lean_ctor_get(v___x_2062_, 1);
lean_inc_ref(v_val_2063_);
lean_dec_ref(v___x_2062_);
v_val_2054_ = v_val_2063_;
goto v___jp_2053_;
}
case 1:
{
lean_object* v_kind_2064_; 
v_kind_2064_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_kind_2064_);
if (lean_obj_tag(v_kind_2064_) == 1)
{
lean_object* v_pre_2065_; 
v_pre_2065_ = lean_ctor_get(v_kind_2064_, 0);
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
lean_inc(v_pre_2067_);
if (lean_obj_tag(v_pre_2067_) == 1)
{
lean_object* v_pre_2068_; 
v_pre_2068_ = lean_ctor_get(v_pre_2067_, 0);
if (lean_obj_tag(v_pre_2068_) == 0)
{
lean_object* v_str_2069_; lean_object* v_str_2070_; lean_object* v_str_2071_; lean_object* v_str_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_str_2069_ = lean_ctor_get(v_kind_2064_, 1);
lean_inc_ref(v_str_2069_);
lean_dec_ref(v_kind_2064_);
v_str_2070_ = lean_ctor_get(v_pre_2065_, 1);
lean_inc_ref(v_str_2070_);
lean_dec_ref(v_pre_2065_);
v_str_2071_ = lean_ctor_get(v_pre_2066_, 1);
lean_inc_ref(v_str_2071_);
lean_dec_ref(v_pre_2066_);
v_str_2072_ = lean_ctor_get(v_pre_2067_, 1);
lean_inc_ref(v_str_2072_);
lean_dec_ref(v_pre_2067_);
v___x_2073_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0));
v___x_2074_ = lean_string_dec_eq(v_str_2072_, v___x_2073_);
lean_dec_ref(v_str_2072_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v_str_2071_);
lean_dec_ref(v_str_2070_);
lean_dec_ref(v_str_2069_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
else
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2076_ = lean_string_dec_eq(v_str_2071_, v___x_2075_);
lean_dec_ref(v_str_2071_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v_str_2070_);
lean_dec_ref(v_str_2069_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2078_ = lean_string_dec_eq(v_str_2070_, v___x_2077_);
lean_dec_ref(v_str_2070_);
if (v___x_2078_ == 0)
{
lean_dec_ref(v_str_2069_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
else
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2080_ = lean_string_dec_eq(v_str_2069_, v___x_2079_);
lean_dec_ref(v_str_2069_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_2081_);
lean_dec_ref(v___x_2062_);
if (lean_obj_tag(v___x_2082_) == 2)
{
lean_object* v_val_2083_; 
lean_dec(v_stx_2043_);
v_val_2083_ = lean_ctor_get(v___x_2082_, 1);
lean_inc_ref(v_val_2083_);
lean_dec_ref(v___x_2082_);
v_val_2054_ = v_val_2083_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v___x_2082_);
v___x_2084_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2043_);
v___x_2085_ = l_Lean_MessageData_ofSyntax(v_stx_2043_);
v___x_2086_ = l_Lean_indentD(v___x_2085_);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2084_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2043_, v___x_2087_, v___y_2044_, v___y_2045_);
lean_dec(v_stx_2043_);
return v___x_2088_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2067_);
lean_dec_ref(v_pre_2066_);
lean_dec_ref(v_pre_2065_);
lean_dec_ref(v_kind_2064_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
}
else
{
lean_dec_ref(v_pre_2066_);
lean_dec(v_pre_2067_);
lean_dec_ref(v_pre_2065_);
lean_dec_ref(v_kind_2064_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
}
else
{
lean_dec_ref(v_pre_2065_);
lean_dec(v_pre_2066_);
lean_dec_ref(v_kind_2064_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
}
else
{
lean_dec(v_pre_2065_);
lean_dec_ref(v_kind_2064_);
lean_dec_ref(v___x_2062_);
goto v___jp_2047_;
}
}
else
{
lean_dec_ref(v___x_2062_);
lean_dec(v_kind_2064_);
goto v___jp_2047_;
}
}
default: 
{
lean_dec(v___x_2062_);
goto v___jp_2047_;
}
}
v___jp_2047_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2048_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2043_);
v___x_2049_ = l_Lean_MessageData_ofSyntax(v_stx_2043_);
v___x_2050_ = l_Lean_indentD(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2043_, v___x_2051_, v___y_2044_, v___y_2045_);
lean_dec(v_stx_2043_);
return v___x_2052_;
}
v___jp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = lean_string_utf8_byte_size(v_val_2054_);
v___x_2057_ = lean_unsigned_to_nat(2u);
v___x_2058_ = lean_nat_sub(v___x_2056_, v___x_2057_);
v___x_2059_ = lean_string_utf8_extract(v_val_2054_, v___x_2055_, v___x_2058_);
lean_dec(v___x_2058_);
lean_dec_ref(v_val_2054_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2094_, size_t v_sz_2095_, size_t v_i_2096_, lean_object* v_b_2097_){
_start:
{
lean_object* v_a_2099_; uint8_t v___x_2103_; 
v___x_2103_ = lean_usize_dec_lt(v_i_2096_, v_sz_2095_);
if (v___x_2103_ == 0)
{
return v_b_2097_;
}
else
{
lean_object* v_a_2104_; lean_object* v_fst_2105_; lean_object* v_snd_2106_; lean_object* v_out_2107_; uint8_t v___x_2108_; 
v_a_2104_ = lean_array_uget_borrowed(v_as_2094_, v_i_2096_);
v_fst_2105_ = lean_ctor_get(v_a_2104_, 0);
v_snd_2106_ = lean_ctor_get(v_a_2104_, 1);
v_out_2107_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2108_ = lean_string_dec_eq(v_snd_2106_, v_out_2107_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2109_ = lean_unbox(v_fst_2105_);
v___x_2110_ = l_Lean_Diff_Action_linePrefix(v___x_2109_);
v___x_2111_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2112_ = lean_string_append(v___x_2110_, v___x_2111_);
v___x_2113_ = lean_string_append(v___x_2112_, v_snd_2106_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2115_ = lean_string_append(v___x_2113_, v___x_2114_);
v___x_2116_ = lean_string_append(v_b_2097_, v___x_2115_);
lean_dec_ref(v___x_2115_);
v_a_2099_ = v___x_2116_;
goto v___jp_2098_;
}
else
{
uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2117_ = lean_unbox(v_fst_2105_);
v___x_2118_ = l_Lean_Diff_Action_linePrefix(v___x_2117_);
v___x_2119_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
v___x_2121_ = lean_string_append(v_b_2097_, v___x_2120_);
lean_dec_ref(v___x_2120_);
v_a_2099_ = v___x_2121_;
goto v___jp_2098_;
}
}
v___jp_2098_:
{
size_t v___x_2100_; size_t v___x_2101_; 
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2096_, v___x_2100_);
v_i_2096_ = v___x_2101_;
v_b_2097_ = v_a_2099_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2122_, lean_object* v_sz_2123_, lean_object* v_i_2124_, lean_object* v_b_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2123_);
lean_dec(v_sz_2123_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2124_);
lean_dec(v_i_2124_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2122_, v_sz_boxed_2126_, v_i_boxed_2127_, v_b_2125_);
lean_dec_ref(v_as_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2129_){
_start:
{
lean_object* v_out_2130_; size_t v_sz_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v_out_2130_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2131_ = lean_array_size(v_lines_2129_);
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2129_, v_sz_2131_, v___x_2132_, v_out_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2134_);
lean_dec_ref(v_lines_2134_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2136_, lean_object* v_as_x27_2137_, lean_object* v_b_2138_){
_start:
{
if (lean_obj_tag(v_as_x27_2137_) == 0)
{
lean_object* v___x_2140_; 
lean_dec_ref(v_filterFn_2136_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_b_2138_);
return v___x_2140_;
}
else
{
lean_object* v_head_2141_; uint8_t v_isSilent_2142_; 
v_head_2141_ = lean_ctor_get(v_as_x27_2137_, 0);
v_isSilent_2142_ = lean_ctor_get_uint8(v_head_2141_, sizeof(void*)*5 + 2);
if (v_isSilent_2142_ == 0)
{
lean_object* v_tail_2143_; lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2165_; 
v_tail_2143_ = lean_ctor_get(v_as_x27_2137_, 1);
v_fst_2144_ = lean_ctor_get(v_b_2138_, 0);
v_snd_2145_ = lean_ctor_get(v_b_2138_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_b_2138_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2147_ = v_b_2138_;
v_isShared_2148_ = v_isSharedCheck_2165_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_snd_2145_);
lean_inc(v_fst_2144_);
lean_dec(v_b_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2165_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
lean_inc_ref(v_filterFn_2136_);
lean_inc(v_head_2141_);
v___x_2149_ = lean_apply_1(v_filterFn_2136_, v_head_2141_);
v___x_2150_ = lean_unbox(v___x_2149_);
switch(v___x_2150_)
{
case 0:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_inc(v_head_2141_);
v___x_2151_ = l_Lean_MessageLog_add(v_head_2141_, v_fst_2144_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2151_);
v___x_2153_ = v___x_2147_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_snd_2145_);
v___x_2153_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_as_x27_2137_ = v_tail_2143_;
v_b_2138_ = v___x_2153_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2157_; 
if (v_isShared_2148_ == 0)
{
v___x_2157_ = v___x_2147_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_fst_2144_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_snd_2145_);
v___x_2157_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
v_as_x27_2137_ = v_tail_2143_;
v_b_2138_ = v___x_2157_;
goto _start;
}
}
default: 
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_inc(v_head_2141_);
v___x_2160_ = l_Lean_MessageLog_add(v_head_2141_, v_snd_2145_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2160_);
v___x_2162_ = v___x_2147_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_fst_2144_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_as_x27_2137_ = v_tail_2143_;
v_b_2138_ = v___x_2162_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2166_; lean_object* v_fst_2167_; lean_object* v_snd_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2176_; 
v_tail_2166_ = lean_ctor_get(v_as_x27_2137_, 1);
v_fst_2167_ = lean_ctor_get(v_b_2138_, 0);
v_snd_2168_ = lean_ctor_get(v_b_2138_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_b_2138_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2170_ = v_b_2138_;
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_snd_2168_);
lean_inc(v_fst_2167_);
lean_dec(v_b_2138_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_fst_2167_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_snd_2168_);
v___x_2173_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
v_as_x27_2137_ = v_tail_2166_;
v_b_2138_ = v___x_2173_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2177_, lean_object* v_as_x27_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2177_, v_as_x27_2178_, v_b_2179_);
lean_dec(v_as_x27_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2182_, lean_object* v_a_2183_, uint8_t v_b_2184_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = 0;
switch(lean_obj_tag(v_a_2183_))
{
case 0:
{
uint8_t v___x_2186_; 
lean_dec_ref(v_a_2183_);
v___x_2186_ = 1;
return v___x_2186_;
}
case 1:
{
lean_object* v_pos_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2200_; 
v_pos_2187_ = lean_ctor_get(v_a_2183_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2189_ = v_a_2183_;
v_isShared_2190_ = v_isSharedCheck_2200_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_pos_2187_);
lean_dec(v_a_2183_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2200_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_str_2191_; lean_object* v_startInclusive_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v_str_2191_ = lean_ctor_get(v_s_2182_, 0);
v_startInclusive_2192_ = lean_ctor_get(v_s_2182_, 1);
v___x_2193_ = lean_nat_add(v_startInclusive_2192_, v_pos_2187_);
lean_dec(v_pos_2187_);
v___x_2194_ = lean_string_utf8_next_fast(v_str_2191_, v___x_2193_);
lean_dec(v___x_2193_);
v___x_2195_ = lean_nat_sub(v___x_2194_, v_startInclusive_2192_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2195_);
v___x_2197_ = v___x_2189_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
v_a_2183_ = v___x_2197_;
v_b_2184_ = v___x_2185_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2201_; lean_object* v_table_2202_; lean_object* v_stackPos_2203_; lean_object* v_needlePos_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2257_; 
v_needle_2201_ = lean_ctor_get(v_a_2183_, 0);
v_table_2202_ = lean_ctor_get(v_a_2183_, 1);
v_stackPos_2203_ = lean_ctor_get(v_a_2183_, 2);
v_needlePos_2204_ = lean_ctor_get(v_a_2183_, 3);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2206_ = v_a_2183_;
v_isShared_2207_ = v_isSharedCheck_2257_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_needlePos_2204_);
lean_inc(v_stackPos_2203_);
lean_inc(v_table_2202_);
lean_inc(v_needle_2201_);
lean_dec(v_a_2183_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2257_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_str_2208_; lean_object* v_startInclusive_2209_; lean_object* v_endExclusive_2210_; lean_object* v_str_2211_; lean_object* v_startInclusive_2212_; lean_object* v_endExclusive_2213_; lean_object* v_basePos_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v_str_2208_ = lean_ctor_get(v_needle_2201_, 0);
v_startInclusive_2209_ = lean_ctor_get(v_needle_2201_, 1);
v_endExclusive_2210_ = lean_ctor_get(v_needle_2201_, 2);
v_str_2211_ = lean_ctor_get(v_s_2182_, 0);
v_startInclusive_2212_ = lean_ctor_get(v_s_2182_, 1);
v_endExclusive_2213_ = lean_ctor_get(v_s_2182_, 2);
v_basePos_2214_ = lean_nat_sub(v_stackPos_2203_, v_needlePos_2204_);
v___x_2215_ = lean_nat_sub(v_endExclusive_2210_, v_startInclusive_2209_);
v___x_2216_ = lean_nat_add(v_basePos_2214_, v___x_2215_);
v___x_2217_ = lean_nat_sub(v_endExclusive_2213_, v_startInclusive_2212_);
v___x_2218_ = lean_nat_dec_le(v___x_2216_, v___x_2217_);
lean_dec(v___x_2216_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; 
lean_dec(v___x_2215_);
lean_del_object(v___x_2206_);
lean_dec(v_needlePos_2204_);
lean_dec(v_stackPos_2203_);
lean_dec_ref(v_table_2202_);
lean_dec_ref(v_needle_2201_);
v___x_2219_ = lean_nat_dec_lt(v_basePos_2214_, v___x_2217_);
lean_dec(v___x_2217_);
lean_dec(v_basePos_2214_);
if (v___x_2219_ == 0)
{
return v_b_2184_;
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_box(3);
v_a_2183_ = v___x_2220_;
v_b_2184_ = v___x_2185_;
goto _start;
}
}
else
{
lean_object* v___x_2222_; uint8_t v_stackByte_2223_; lean_object* v___x_2224_; uint8_t v_patByte_2225_; uint8_t v___x_2226_; 
lean_dec(v___x_2217_);
lean_dec(v_basePos_2214_);
v___x_2222_ = lean_nat_add(v_startInclusive_2212_, v_stackPos_2203_);
v_stackByte_2223_ = lean_string_get_byte_fast(v_str_2211_, v___x_2222_);
v___x_2224_ = lean_nat_add(v_startInclusive_2209_, v_needlePos_2204_);
v_patByte_2225_ = lean_string_get_byte_fast(v_str_2208_, v___x_2224_);
v___x_2226_ = lean_uint8_dec_eq(v_stackByte_2223_, v_patByte_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
lean_dec(v___x_2215_);
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_nat_dec_eq(v_needlePos_2204_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_newNeedlePos_2231_; uint8_t v___x_2232_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_sub(v_needlePos_2204_, v___x_2229_);
lean_dec(v_needlePos_2204_);
v_newNeedlePos_2231_ = lean_array_fget_borrowed(v_table_2202_, v___x_2230_);
lean_dec(v___x_2230_);
v___x_2232_ = lean_nat_dec_eq(v_newNeedlePos_2231_, v___x_2227_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2234_; 
lean_inc(v_newNeedlePos_2231_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v_newNeedlePos_2231_);
v___x_2234_ = v___x_2206_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_stackPos_2203_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_newNeedlePos_2231_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v_a_2183_ = v___x_2234_;
v_b_2184_ = v___x_2185_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2237_; lean_object* v___x_2239_; 
v_nextStackPos_2237_ = l_String_Slice_posGE___redArg(v_s_2182_, v_stackPos_2203_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v___x_2227_);
lean_ctor_set(v___x_2206_, 2, v_nextStackPos_2237_);
v___x_2239_ = v___x_2206_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_nextStackPos_2237_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v___x_2227_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v_a_2183_ = v___x_2239_;
v_b_2184_ = v___x_2185_;
goto _start;
}
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_nextStackPos_2244_; lean_object* v___x_2246_; 
lean_dec(v_needlePos_2204_);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_add(v_stackPos_2203_, v___x_2242_);
lean_dec(v_stackPos_2203_);
v_nextStackPos_2244_ = l_String_Slice_posGE___redArg(v_s_2182_, v___x_2243_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v___x_2227_);
lean_ctor_set(v___x_2206_, 2, v_nextStackPos_2244_);
v___x_2246_ = v___x_2206_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_nextStackPos_2244_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v___x_2227_);
v___x_2246_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
v_a_2183_ = v___x_2246_;
v_b_2184_ = v___x_2185_;
goto _start;
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v_nextNeedlePos_2250_; uint8_t v___x_2251_; 
v___x_2249_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2250_ = lean_nat_add(v_needlePos_2204_, v___x_2249_);
lean_dec(v_needlePos_2204_);
v___x_2251_ = lean_nat_dec_eq(v_nextNeedlePos_2250_, v___x_2215_);
lean_dec(v___x_2215_);
if (v___x_2251_ == 0)
{
lean_object* v_nextStackPos_2252_; lean_object* v___x_2254_; 
v_nextStackPos_2252_ = lean_nat_add(v_stackPos_2203_, v___x_2249_);
lean_dec(v_stackPos_2203_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v_nextNeedlePos_2250_);
lean_ctor_set(v___x_2206_, 2, v_nextStackPos_2252_);
v___x_2254_ = v___x_2206_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_nextStackPos_2252_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_nextNeedlePos_2250_);
v___x_2254_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
v_a_2183_ = v___x_2254_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2250_);
lean_del_object(v___x_2206_);
lean_dec(v_stackPos_2203_);
lean_dec_ref(v_table_2202_);
lean_dec_ref(v_needle_2201_);
return v___x_2251_;
}
}
}
}
}
default: 
{
return v_b_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2258_, lean_object* v_a_2259_, lean_object* v_b_2260_){
_start:
{
uint8_t v_b_boxed_2261_; uint8_t v_res_2262_; lean_object* v_r_2263_; 
v_b_boxed_2261_ = lean_unbox(v_b_2260_);
v_res_2262_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2258_, v_a_2259_, v_b_boxed_2261_);
lean_dec_ref(v_s_2258_);
v_r_2263_ = lean_box(v_res_2262_);
return v_r_2263_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2264_, lean_object* v_s_2265_){
_start:
{
lean_object* v___y_2267_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_string_utf8_byte_size(v___x_2264_);
v___x_2272_ = lean_nat_dec_eq(v___x_2271_, v___x_2270_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2264_);
lean_ctor_set(v___x_2273_, 1, v___x_2270_);
lean_ctor_set(v___x_2273_, 2, v___x_2271_);
v___x_2274_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
lean_ctor_set(v___x_2275_, 2, v___x_2270_);
lean_ctor_set(v___x_2275_, 3, v___x_2270_);
v___y_2267_ = v___x_2275_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2276_; 
lean_dec_ref(v___x_2264_);
v___x_2276_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2267_ = v___x_2276_;
goto v___jp_2266_;
}
v___jp_2266_:
{
uint8_t v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = 0;
v___x_2269_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2265_, v___y_2267_, v___x_2268_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2277_, lean_object* v_s_2278_){
_start:
{
uint8_t v_res_2279_; lean_object* v_r_2280_; 
v_res_2279_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2277_, v_s_2278_);
lean_dec_ref(v_s_2278_);
v_r_2280_ = lean_box(v_res_2279_);
return v_r_2280_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2281_, uint8_t v_suppressElabErrors_2282_, lean_object* v_x_2283_){
_start:
{
if (lean_obj_tag(v_x_2283_) == 1)
{
lean_object* v_pre_2284_; 
v_pre_2284_ = lean_ctor_get(v_x_2283_, 0);
if (lean_obj_tag(v_pre_2284_) == 0)
{
lean_object* v_str_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v_str_2285_ = lean_ctor_get(v_x_2283_, 1);
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2287_ = lean_string_dec_eq(v_str_2285_, v___x_2286_);
if (v___x_2287_ == 0)
{
return v___y_2281_;
}
else
{
return v_suppressElabErrors_2282_;
}
}
else
{
return v___y_2281_;
}
}
else
{
return v___y_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2288_, lean_object* v_suppressElabErrors_2289_, lean_object* v_x_2290_){
_start:
{
uint8_t v___y_29379__boxed_2291_; uint8_t v_suppressElabErrors_boxed_2292_; uint8_t v_res_2293_; lean_object* v_r_2294_; 
v___y_29379__boxed_2291_ = lean_unbox(v___y_2288_);
v_suppressElabErrors_boxed_2292_ = lean_unbox(v_suppressElabErrors_2289_);
v_res_2293_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29379__boxed_2291_, v_suppressElabErrors_boxed_2292_, v_x_2290_);
lean_dec(v_x_2290_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2295_, lean_object* v_msgData_2296_, uint8_t v_severity_2297_, uint8_t v_isSilent_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
uint8_t v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; uint8_t v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2395_; uint8_t v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; uint8_t v___y_2403_; uint8_t v___y_2404_; uint8_t v___y_2405_; uint8_t v___x_2420_; uint8_t v___y_2422_; uint8_t v___y_2423_; uint8_t v___y_2424_; uint8_t v___y_2426_; uint8_t v___x_2438_; 
v___x_2420_ = 2;
v___x_2438_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2297_, v___x_2420_);
if (v___x_2438_ == 0)
{
v___y_2426_ = v___x_2438_;
goto v___jp_2425_;
}
else
{
uint8_t v___x_2439_; 
lean_inc_ref(v_msgData_2296_);
v___x_2439_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2296_);
v___y_2426_ = v___x_2439_;
goto v___jp_2425_;
}
v___jp_2302_:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Elab_Command_getScope___redArg(v___y_2310_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = l_Lean_Elab_Command_getScope___redArg(v___y_2310_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2349_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2349_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2349_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v_currNamespace_2319_; lean_object* v_openDecls_2320_; lean_object* v_env_2321_; lean_object* v_messages_2322_; lean_object* v_scopes_2323_; lean_object* v_usedQuotCtxts_2324_; lean_object* v_nextMacroScope_2325_; lean_object* v_maxRecDepth_2326_; lean_object* v_ngen_2327_; lean_object* v_auxDeclNGen_2328_; lean_object* v_infoState_2329_; lean_object* v_traceState_2330_; lean_object* v_snapshotTasks_2331_; lean_object* v_newDecls_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2348_; 
v___x_2318_ = lean_st_ref_take(v___y_2310_);
v_currNamespace_2319_ = lean_ctor_get(v_a_2312_, 2);
lean_inc(v_currNamespace_2319_);
lean_dec(v_a_2312_);
v_openDecls_2320_ = lean_ctor_get(v_a_2314_, 3);
lean_inc(v_openDecls_2320_);
lean_dec(v_a_2314_);
v_env_2321_ = lean_ctor_get(v___x_2318_, 0);
v_messages_2322_ = lean_ctor_get(v___x_2318_, 1);
v_scopes_2323_ = lean_ctor_get(v___x_2318_, 2);
v_usedQuotCtxts_2324_ = lean_ctor_get(v___x_2318_, 3);
v_nextMacroScope_2325_ = lean_ctor_get(v___x_2318_, 4);
v_maxRecDepth_2326_ = lean_ctor_get(v___x_2318_, 5);
v_ngen_2327_ = lean_ctor_get(v___x_2318_, 6);
v_auxDeclNGen_2328_ = lean_ctor_get(v___x_2318_, 7);
v_infoState_2329_ = lean_ctor_get(v___x_2318_, 8);
v_traceState_2330_ = lean_ctor_get(v___x_2318_, 9);
v_snapshotTasks_2331_ = lean_ctor_get(v___x_2318_, 10);
v_newDecls_2332_ = lean_ctor_get(v___x_2318_, 11);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2334_ = v___x_2318_;
v_isShared_2335_ = v_isSharedCheck_2348_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_newDecls_2332_);
lean_inc(v_snapshotTasks_2331_);
lean_inc(v_traceState_2330_);
lean_inc(v_infoState_2329_);
lean_inc(v_auxDeclNGen_2328_);
lean_inc(v_ngen_2327_);
lean_inc(v_maxRecDepth_2326_);
lean_inc(v_nextMacroScope_2325_);
lean_inc(v_usedQuotCtxts_2324_);
lean_inc(v_scopes_2323_);
lean_inc(v_messages_2322_);
lean_inc(v_env_2321_);
lean_dec(v___x_2318_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2348_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_currNamespace_2319_);
lean_ctor_set(v___x_2336_, 1, v_openDecls_2320_);
v___x_2337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___y_2304_);
lean_inc_ref(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2338_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2338_, 0, v___y_2308_);
lean_ctor_set(v___x_2338_, 1, v___y_2305_);
lean_ctor_set(v___x_2338_, 2, v___y_2306_);
lean_ctor_set(v___x_2338_, 3, v___y_2309_);
lean_ctor_set(v___x_2338_, 4, v___x_2337_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*5, v___y_2307_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*5 + 1, v___y_2303_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*5 + 2, v_isSilent_2298_);
v___x_2339_ = l_Lean_MessageLog_add(v___x_2338_, v_messages_2322_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v___x_2339_);
v___x_2341_ = v___x_2334_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_env_2321_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_scopes_2323_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_usedQuotCtxts_2324_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_nextMacroScope_2325_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_maxRecDepth_2326_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_ngen_2327_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v_auxDeclNGen_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_infoState_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 9, v_traceState_2330_);
lean_ctor_set(v_reuseFailAlloc_2347_, 10, v_snapshotTasks_2331_);
lean_ctor_set(v_reuseFailAlloc_2347_, 11, v_newDecls_2332_);
v___x_2341_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2342_ = lean_st_ref_set(v___y_2310_, v___x_2341_);
v___x_2343_ = lean_box(0);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2343_);
v___x_2345_ = v___x_2316_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2312_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v___y_2304_);
v_a_2350_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2313_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2313_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v___y_2304_);
v_a_2358_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2311_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2311_);
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
v___jp_2366_:
{
lean_object* v_fileName_2372_; lean_object* v_fileMap_2373_; uint8_t v_suppressElabErrors_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2393_; 
v_fileName_2372_ = lean_ctor_get(v___y_2299_, 0);
v_fileMap_2373_ = lean_ctor_get(v___y_2299_, 1);
v_suppressElabErrors_2374_ = lean_ctor_get_uint8(v___y_2299_, sizeof(void*)*10);
v___x_2375_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2296_);
v___x_2376_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2375_, v___y_2300_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2393_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2393_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_inc_ref_n(v_fileMap_2373_, 2);
v___x_2381_ = l_Lean_FileMap_toPosition(v_fileMap_2373_, v___y_2369_);
lean_dec(v___y_2369_);
v___x_2382_ = l_Lean_FileMap_toPosition(v_fileMap_2373_, v___y_2371_);
lean_dec(v___y_2371_);
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2374_ == 0)
{
lean_del_object(v___x_2379_);
v___y_2303_ = v___y_2368_;
v___y_2304_ = v_a_2377_;
v___y_2305_ = v___x_2381_;
v___y_2306_ = v___x_2383_;
v___y_2307_ = v___y_2370_;
v___y_2308_ = v_fileName_2372_;
v___y_2309_ = v___x_2384_;
v___y_2310_ = v___y_2300_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___f_2387_; uint8_t v___x_2388_; 
v___x_2385_ = lean_box(v___y_2367_);
v___x_2386_ = lean_box(v_suppressElabErrors_2374_);
v___f_2387_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2387_, 0, v___x_2385_);
lean_closure_set(v___f_2387_, 1, v___x_2386_);
lean_inc(v_a_2377_);
v___x_2388_ = l_Lean_MessageData_hasTag(v___f_2387_, v_a_2377_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_dec_ref(v___x_2383_);
lean_dec_ref(v___x_2381_);
lean_dec(v_a_2377_);
v___x_2389_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2389_);
v___x_2391_ = v___x_2379_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
else
{
lean_del_object(v___x_2379_);
v___y_2303_ = v___y_2368_;
v___y_2304_ = v_a_2377_;
v___y_2305_ = v___x_2381_;
v___y_2306_ = v___x_2383_;
v___y_2307_ = v___y_2370_;
v___y_2308_ = v_fileName_2372_;
v___y_2309_ = v___x_2384_;
v___y_2310_ = v___y_2300_;
goto v___jp_2302_;
}
}
}
}
v___jp_2394_:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Syntax_getTailPos_x3f(v___y_2397_, v___y_2398_);
lean_dec(v___y_2397_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_inc(v___y_2399_);
v___y_2367_ = v___y_2395_;
v___y_2368_ = v___y_2396_;
v___y_2369_ = v___y_2399_;
v___y_2370_ = v___y_2398_;
v___y_2371_ = v___y_2399_;
goto v___jp_2366_;
}
else
{
lean_object* v_val_2401_; 
v_val_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_val_2401_);
lean_dec_ref(v___x_2400_);
v___y_2367_ = v___y_2395_;
v___y_2368_ = v___y_2396_;
v___y_2369_ = v___y_2399_;
v___y_2370_ = v___y_2398_;
v___y_2371_ = v_val_2401_;
goto v___jp_2366_;
}
}
v___jp_2402_:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Elab_Command_getRef___redArg(v___y_2299_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v_ref_2408_; lean_object* v___x_2409_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v_ref_2408_ = l_Lean_replaceRef(v_ref_2295_, v_a_2407_);
lean_dec(v_a_2407_);
v___x_2409_ = l_Lean_Syntax_getPos_x3f(v_ref_2408_, v___y_2404_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v___y_2395_ = v___y_2403_;
v___y_2396_ = v___y_2405_;
v___y_2397_ = v_ref_2408_;
v___y_2398_ = v___y_2404_;
v___y_2399_ = v___x_2410_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2411_; 
v_val_2411_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_val_2411_);
lean_dec_ref(v___x_2409_);
v___y_2395_ = v___y_2403_;
v___y_2396_ = v___y_2405_;
v___y_2397_ = v_ref_2408_;
v___y_2398_ = v___y_2404_;
v___y_2399_ = v_val_2411_;
goto v___jp_2394_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_msgData_2296_);
v_a_2412_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2406_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2406_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
v___jp_2421_:
{
if (v___y_2424_ == 0)
{
v___y_2403_ = v___y_2422_;
v___y_2404_ = v___y_2423_;
v___y_2405_ = v_severity_2297_;
goto v___jp_2402_;
}
else
{
v___y_2403_ = v___y_2422_;
v___y_2404_ = v___y_2423_;
v___y_2405_ = v___x_2420_;
goto v___jp_2402_;
}
}
v___jp_2425_:
{
if (v___y_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v_scopes_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v_opts_2431_; uint8_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2427_ = lean_st_ref_get(v___y_2300_);
v_scopes_2428_ = lean_ctor_get(v___x_2427_, 2);
lean_inc(v_scopes_2428_);
lean_dec(v___x_2427_);
v___x_2429_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2430_ = l_List_head_x21___redArg(v___x_2429_, v_scopes_2428_);
lean_dec(v_scopes_2428_);
v_opts_2431_ = lean_ctor_get(v___x_2430_, 1);
lean_inc_ref(v_opts_2431_);
lean_dec(v___x_2430_);
v___x_2432_ = 1;
v___x_2433_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2297_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v_opts_2431_);
v___y_2422_ = v___y_2426_;
v___y_2423_ = v___y_2426_;
v___y_2424_ = v___x_2433_;
goto v___jp_2421_;
}
else
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = l_Lean_warningAsError;
v___x_2435_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2431_, v___x_2434_);
lean_dec_ref(v_opts_2431_);
v___y_2422_ = v___y_2426_;
v___y_2423_ = v___y_2426_;
v___y_2424_ = v___x_2435_;
goto v___jp_2421_;
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec_ref(v_msgData_2296_);
v___x_2436_ = lean_box(0);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2440_, lean_object* v_msgData_2441_, lean_object* v_severity_2442_, lean_object* v_isSilent_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v_severity_boxed_2447_; uint8_t v_isSilent_boxed_2448_; lean_object* v_res_2449_; 
v_severity_boxed_2447_ = lean_unbox(v_severity_2442_);
v_isSilent_boxed_2448_ = lean_unbox(v_isSilent_2443_);
v_res_2449_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2440_, v_msgData_2441_, v_severity_boxed_2447_, v_isSilent_boxed_2448_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v_ref_2440_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2450_, lean_object* v_msgData_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = 2;
v___x_2456_ = 0;
v___x_2457_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2450_, v_msgData_2451_, v___x_2455_, v___x_2456_, v___y_2452_, v___y_2453_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2458_, lean_object* v_msgData_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2458_, v_msgData_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v_ref_2458_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2464_, lean_object* v___x_2465_, lean_object* v___x_2466_, lean_object* v_a_2467_, lean_object* v_b_2468_){
_start:
{
lean_object* v_it_2470_; lean_object* v_startInclusive_2471_; lean_object* v_endExclusive_2472_; 
if (lean_obj_tag(v_a_2467_) == 0)
{
lean_object* v_currPos_2477_; lean_object* v_searcher_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2507_; 
v_currPos_2477_ = lean_ctor_get(v_a_2467_, 0);
v_searcher_2478_ = lean_ctor_get(v_a_2467_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_a_2467_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2480_ = v_a_2467_;
v_isShared_2481_ = v_isSharedCheck_2507_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_searcher_2478_);
lean_inc(v_currPos_2477_);
lean_dec(v_a_2467_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2507_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_str_2482_; lean_object* v_startInclusive_2483_; lean_object* v_endExclusive_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_str_2482_ = lean_ctor_get(v___x_2465_, 0);
v_startInclusive_2483_ = lean_ctor_get(v___x_2465_, 1);
v_endExclusive_2484_ = lean_ctor_get(v___x_2465_, 2);
v___x_2485_ = lean_nat_sub(v_endExclusive_2484_, v_startInclusive_2483_);
v___x_2486_ = lean_nat_dec_eq(v_searcher_2478_, v___x_2485_);
lean_dec(v___x_2485_);
if (v___x_2486_ == 0)
{
uint32_t v___x_2487_; lean_object* v___x_2488_; uint32_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2487_ = 10;
v___x_2488_ = lean_nat_add(v_startInclusive_2483_, v_searcher_2478_);
v___x_2489_ = lean_string_utf8_get_fast(v_str_2482_, v___x_2488_);
v___x_2490_ = lean_uint32_dec_eq(v___x_2489_, v___x_2487_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_dec(v_searcher_2478_);
v___x_2491_ = lean_string_utf8_next_fast(v_str_2482_, v___x_2488_);
lean_dec(v___x_2488_);
v___x_2492_ = lean_nat_sub(v___x_2491_, v_startInclusive_2483_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2492_);
v___x_2494_ = v___x_2480_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_currPos_2477_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
v_a_2467_ = v___x_2494_;
goto _start;
}
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_slice_2500_; lean_object* v_nextIt_2502_; 
v___x_2497_ = lean_string_utf8_next_fast(v_str_2482_, v___x_2488_);
v___x_2498_ = lean_nat_sub(v___x_2497_, v___x_2488_);
lean_dec(v___x_2488_);
v___x_2499_ = lean_nat_add(v_searcher_2478_, v___x_2498_);
lean_dec(v___x_2498_);
v_slice_2500_ = l_String_Slice_subslice_x21(v___x_2465_, v_currPos_2477_, v_searcher_2478_);
lean_inc(v___x_2499_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2499_);
lean_ctor_set(v___x_2480_, 0, v___x_2499_);
v_nextIt_2502_ = v___x_2480_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___x_2499_);
v_nextIt_2502_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v_startInclusive_2503_; lean_object* v_endExclusive_2504_; 
v_startInclusive_2503_ = lean_ctor_get(v_slice_2500_, 0);
lean_inc(v_startInclusive_2503_);
v_endExclusive_2504_ = lean_ctor_get(v_slice_2500_, 1);
lean_inc(v_endExclusive_2504_);
lean_dec_ref(v_slice_2500_);
v_it_2470_ = v_nextIt_2502_;
v_startInclusive_2471_ = v_startInclusive_2503_;
v_endExclusive_2472_ = v_endExclusive_2504_;
goto v___jp_2469_;
}
}
}
else
{
lean_object* v___x_2506_; 
lean_del_object(v___x_2480_);
lean_dec(v_searcher_2478_);
v___x_2506_ = lean_box(1);
lean_inc(v___x_2466_);
v_it_2470_ = v___x_2506_;
v_startInclusive_2471_ = v_currPos_2477_;
v_endExclusive_2472_ = v___x_2466_;
goto v___jp_2469_;
}
}
}
else
{
lean_dec(v___x_2466_);
lean_dec_ref(v___x_2464_);
return v_b_2468_;
}
v___jp_2469_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_inc_ref(v___x_2464_);
v___x_2473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2464_);
lean_ctor_set(v___x_2473_, 1, v_startInclusive_2471_);
lean_ctor_set(v___x_2473_, 2, v_endExclusive_2472_);
v___x_2474_ = l_String_Slice_toString(v___x_2473_);
lean_dec_ref(v___x_2473_);
v___x_2475_ = lean_array_push(v_b_2468_, v___x_2474_);
v_a_2467_ = v_it_2470_;
v_b_2468_ = v___x_2475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2508_, lean_object* v___x_2509_, lean_object* v___x_2510_, lean_object* v_a_2511_, lean_object* v_b_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2508_, v___x_2509_, v___x_2510_, v_a_2511_, v_b_2512_);
lean_dec_ref(v___x_2509_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2514_, lean_object* v___x_2515_, lean_object* v___x_2516_, lean_object* v_a_2517_, lean_object* v_b_2518_){
_start:
{
lean_object* v_it_2520_; lean_object* v_startInclusive_2521_; lean_object* v_endExclusive_2522_; 
if (lean_obj_tag(v_a_2517_) == 0)
{
lean_object* v_currPos_2527_; lean_object* v_searcher_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2557_; 
v_currPos_2527_ = lean_ctor_get(v_a_2517_, 0);
v_searcher_2528_ = lean_ctor_get(v_a_2517_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_a_2517_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2530_ = v_a_2517_;
v_isShared_2531_ = v_isSharedCheck_2557_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_searcher_2528_);
lean_inc(v_currPos_2527_);
lean_dec(v_a_2517_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2557_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v_str_2532_; lean_object* v_startInclusive_2533_; lean_object* v_endExclusive_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_str_2532_ = lean_ctor_get(v___x_2515_, 0);
v_startInclusive_2533_ = lean_ctor_get(v___x_2515_, 1);
v_endExclusive_2534_ = lean_ctor_get(v___x_2515_, 2);
v___x_2535_ = lean_nat_sub(v_endExclusive_2534_, v_startInclusive_2533_);
v___x_2536_ = lean_nat_dec_eq(v_searcher_2528_, v___x_2535_);
lean_dec(v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; uint32_t v___x_2538_; uint32_t v___x_2539_; uint8_t v___x_2540_; 
v___x_2537_ = lean_nat_add(v_startInclusive_2533_, v_searcher_2528_);
v___x_2538_ = lean_string_utf8_get_fast(v_str_2532_, v___x_2537_);
v___x_2539_ = 10;
v___x_2540_ = lean_uint32_dec_eq(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
lean_dec(v_searcher_2528_);
v___x_2541_ = lean_string_utf8_next_fast(v_str_2532_, v___x_2537_);
lean_dec(v___x_2537_);
v___x_2542_ = lean_nat_sub(v___x_2541_, v_startInclusive_2533_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2542_);
v___x_2544_ = v___x_2530_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_currPos_2527_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; 
v___x_2545_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2514_, v___x_2515_, v___x_2516_, v___x_2544_, v_b_2518_);
return v___x_2545_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_slice_2550_; lean_object* v_nextIt_2552_; 
v___x_2547_ = lean_string_utf8_next_fast(v_str_2532_, v___x_2537_);
v___x_2548_ = lean_nat_sub(v___x_2547_, v___x_2537_);
lean_dec(v___x_2537_);
v___x_2549_ = lean_nat_add(v_searcher_2528_, v___x_2548_);
lean_dec(v___x_2548_);
v_slice_2550_ = l_String_Slice_subslice_x21(v___x_2515_, v_currPos_2527_, v_searcher_2528_);
lean_inc(v___x_2549_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2549_);
lean_ctor_set(v___x_2530_, 0, v___x_2549_);
v_nextIt_2552_ = v___x_2530_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2549_);
v_nextIt_2552_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v_startInclusive_2553_; lean_object* v_endExclusive_2554_; 
v_startInclusive_2553_ = lean_ctor_get(v_slice_2550_, 0);
lean_inc(v_startInclusive_2553_);
v_endExclusive_2554_ = lean_ctor_get(v_slice_2550_, 1);
lean_inc(v_endExclusive_2554_);
lean_dec_ref(v_slice_2550_);
v_it_2520_ = v_nextIt_2552_;
v_startInclusive_2521_ = v_startInclusive_2553_;
v_endExclusive_2522_ = v_endExclusive_2554_;
goto v___jp_2519_;
}
}
}
else
{
lean_object* v___x_2556_; 
lean_del_object(v___x_2530_);
lean_dec(v_searcher_2528_);
v___x_2556_ = lean_box(1);
lean_inc(v___x_2516_);
v_it_2520_ = v___x_2556_;
v_startInclusive_2521_ = v_currPos_2527_;
v_endExclusive_2522_ = v___x_2516_;
goto v___jp_2519_;
}
}
}
else
{
lean_dec(v___x_2516_);
lean_dec_ref(v___x_2514_);
return v_b_2518_;
}
v___jp_2519_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_inc_ref(v___x_2514_);
v___x_2523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2514_);
lean_ctor_set(v___x_2523_, 1, v_startInclusive_2521_);
lean_ctor_set(v___x_2523_, 2, v_endExclusive_2522_);
v___x_2524_ = l_String_Slice_toString(v___x_2523_);
lean_dec_ref(v___x_2523_);
v___x_2525_ = lean_array_push(v_b_2518_, v___x_2524_);
v___x_2526_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2514_, v___x_2515_, v___x_2516_, v_it_2520_, v___x_2525_);
return v___x_2526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2558_, lean_object* v___x_2559_, lean_object* v___x_2560_, lean_object* v_a_2561_, lean_object* v_b_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2558_, v___x_2559_, v___x_2560_, v_a_2561_, v_b_2562_);
lean_dec_ref(v___x_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; lean_object* v_infoState_2568_; uint8_t v_enabled_2569_; 
v___x_2567_ = lean_st_ref_get(v___y_2565_);
v_infoState_2568_ = lean_ctor_get(v___x_2567_, 8);
lean_inc_ref(v_infoState_2568_);
lean_dec(v___x_2567_);
v_enabled_2569_ = lean_ctor_get_uint8(v_infoState_2568_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2568_);
if (v_enabled_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref(v_t_2564_);
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; lean_object* v_infoState_2573_; lean_object* v_env_2574_; lean_object* v_messages_2575_; lean_object* v_scopes_2576_; lean_object* v_usedQuotCtxts_2577_; lean_object* v_nextMacroScope_2578_; lean_object* v_maxRecDepth_2579_; lean_object* v_ngen_2580_; lean_object* v_auxDeclNGen_2581_; lean_object* v_traceState_2582_; lean_object* v_snapshotTasks_2583_; lean_object* v_newDecls_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2606_; 
v___x_2572_ = lean_st_ref_take(v___y_2565_);
v_infoState_2573_ = lean_ctor_get(v___x_2572_, 8);
v_env_2574_ = lean_ctor_get(v___x_2572_, 0);
v_messages_2575_ = lean_ctor_get(v___x_2572_, 1);
v_scopes_2576_ = lean_ctor_get(v___x_2572_, 2);
v_usedQuotCtxts_2577_ = lean_ctor_get(v___x_2572_, 3);
v_nextMacroScope_2578_ = lean_ctor_get(v___x_2572_, 4);
v_maxRecDepth_2579_ = lean_ctor_get(v___x_2572_, 5);
v_ngen_2580_ = lean_ctor_get(v___x_2572_, 6);
v_auxDeclNGen_2581_ = lean_ctor_get(v___x_2572_, 7);
v_traceState_2582_ = lean_ctor_get(v___x_2572_, 9);
v_snapshotTasks_2583_ = lean_ctor_get(v___x_2572_, 10);
v_newDecls_2584_ = lean_ctor_get(v___x_2572_, 11);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2586_ = v___x_2572_;
v_isShared_2587_ = v_isSharedCheck_2606_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_newDecls_2584_);
lean_inc(v_snapshotTasks_2583_);
lean_inc(v_traceState_2582_);
lean_inc(v_infoState_2573_);
lean_inc(v_auxDeclNGen_2581_);
lean_inc(v_ngen_2580_);
lean_inc(v_maxRecDepth_2579_);
lean_inc(v_nextMacroScope_2578_);
lean_inc(v_usedQuotCtxts_2577_);
lean_inc(v_scopes_2576_);
lean_inc(v_messages_2575_);
lean_inc(v_env_2574_);
lean_dec(v___x_2572_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2606_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
uint8_t v_enabled_2588_; lean_object* v_assignment_2589_; lean_object* v_lazyAssignment_2590_; lean_object* v_trees_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2605_; 
v_enabled_2588_ = lean_ctor_get_uint8(v_infoState_2573_, sizeof(void*)*3);
v_assignment_2589_ = lean_ctor_get(v_infoState_2573_, 0);
v_lazyAssignment_2590_ = lean_ctor_get(v_infoState_2573_, 1);
v_trees_2591_ = lean_ctor_get(v_infoState_2573_, 2);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_infoState_2573_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2593_ = v_infoState_2573_;
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_trees_2591_);
lean_inc(v_lazyAssignment_2590_);
lean_inc(v_assignment_2589_);
lean_dec(v_infoState_2573_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = l_Lean_PersistentArray_push___redArg(v_trees_2591_, v_t_2564_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 2, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_assignment_2589_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_lazyAssignment_2590_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v___x_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2604_, sizeof(void*)*3, v_enabled_2588_);
v___x_2597_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2599_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 8, v___x_2597_);
v___x_2599_ = v___x_2586_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_env_2574_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_messages_2575_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_scopes_2576_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_usedQuotCtxts_2577_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_nextMacroScope_2578_);
lean_ctor_set(v_reuseFailAlloc_2603_, 5, v_maxRecDepth_2579_);
lean_ctor_set(v_reuseFailAlloc_2603_, 6, v_ngen_2580_);
lean_ctor_set(v_reuseFailAlloc_2603_, 7, v_auxDeclNGen_2581_);
lean_ctor_set(v_reuseFailAlloc_2603_, 8, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2603_, 9, v_traceState_2582_);
lean_ctor_set(v_reuseFailAlloc_2603_, 10, v_snapshotTasks_2583_);
lean_ctor_set(v_reuseFailAlloc_2603_, 11, v_newDecls_2584_);
v___x_2599_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_st_ref_set(v___y_2565_, v___x_2599_);
v___x_2601_ = lean_box(0);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2607_, v___y_2608_);
lean_dec(v___y_2608_);
return v_res_2610_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_unsigned_to_nat(32u);
v___x_2612_ = lean_mk_empty_array_with_capacity(v___x_2611_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2614_ = ((size_t)5ULL);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_unsigned_to_nat(32u);
v___x_2617_ = lean_mk_empty_array_with_capacity(v___x_2616_);
v___x_2618_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2619_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___x_2617_);
lean_ctor_set(v___x_2619_, 2, v___x_2615_);
lean_ctor_set(v___x_2619_, 3, v___x_2615_);
lean_ctor_set_usize(v___x_2619_, 4, v___x_2614_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; lean_object* v_infoState_2625_; uint8_t v_enabled_2626_; 
v___x_2624_ = lean_st_ref_get(v___y_2622_);
v_infoState_2625_ = lean_ctor_get(v___x_2624_, 8);
lean_inc_ref(v_infoState_2625_);
lean_dec(v___x_2624_);
v_enabled_2626_ = lean_ctor_get_uint8(v_infoState_2625_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2625_);
if (v_enabled_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v_t_2620_);
v___x_2627_ = lean_box(0);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_t_2620_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2630_, v___y_2622_);
return v___x_2631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2637_, lean_object* v_original_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2660_; 
v_fst_2640_ = lean_ctor_get(v_a_2639_, 0);
v_snd_2641_ = lean_ctor_get(v_a_2639_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_a_2639_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2643_ = v_a_2639_;
v_isShared_2644_ = v_isSharedCheck_2660_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snd_2641_);
lean_inc(v_fst_2640_);
lean_dec(v_a_2639_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2660_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_nat_dec_lt(v_snd_2641_, v___x_2637_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2647_; 
if (v_isShared_2644_ == 0)
{
v___x_2647_ = v___x_2643_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_fst_2640_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_snd_2641_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2649_ = 1;
v___x_2650_ = lean_array_fget_borrowed(v_original_2638_, v_snd_2641_);
v___x_2651_ = lean_box(v___x_2649_);
lean_inc(v___x_2650_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 1, v___x_2650_);
lean_ctor_set(v___x_2643_, 0, v___x_2651_);
v___x_2653_ = v___x_2643_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2650_);
v___x_2653_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2654_ = lean_array_push(v_fst_2640_, v___x_2653_);
v___x_2655_ = lean_unsigned_to_nat(1u);
v___x_2656_ = lean_nat_add(v_snd_2641_, v___x_2655_);
lean_dec(v_snd_2641_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2654_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v_a_2639_ = v___x_2657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2661_, lean_object* v_original_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2661_, v_original_2662_, v_a_2663_);
lean_dec_ref(v_original_2662_);
lean_dec(v___x_2661_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v_original_2665_, lean_object* v___x_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_fst_2669_; lean_object* v_snd_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2695_; 
v_fst_2669_ = lean_ctor_get(v_a_2668_, 0);
v_snd_2670_ = lean_ctor_get(v_a_2668_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2668_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2672_ = v_a_2668_;
v_isShared_2673_ = v_isSharedCheck_2695_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snd_2670_);
lean_inc(v_fst_2669_);
lean_dec(v_a_2668_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2695_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; uint8_t v___y_2676_; uint8_t v___x_2691_; 
v___x_2674_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2691_ = lean_nat_dec_lt(v_snd_2670_, v___x_2666_);
if (v___x_2691_ == 0)
{
v___y_2676_ = v___x_2691_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = lean_array_get_borrowed(v___x_2674_, v_original_2665_, v_snd_2670_);
v___x_2693_ = lean_string_dec_eq(v___x_2692_, v_a_2667_);
if (v___x_2693_ == 0)
{
v___y_2676_ = v___x_2691_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2694_; 
lean_del_object(v___x_2672_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_fst_2669_);
lean_ctor_set(v___x_2694_, 1, v_snd_2670_);
return v___x_2694_;
}
}
v___jp_2675_:
{
if (v___y_2676_ == 0)
{
lean_object* v___x_2678_; 
if (v_isShared_2673_ == 0)
{
v___x_2678_ = v___x_2672_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_snd_2670_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2680_ = 1;
v___x_2681_ = lean_array_get_borrowed(v___x_2674_, v_original_2665_, v_snd_2670_);
v___x_2682_ = lean_box(v___x_2680_);
lean_inc(v___x_2681_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2681_);
lean_ctor_set(v___x_2672_, 0, v___x_2682_);
v___x_2684_ = v___x_2672_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2681_);
v___x_2684_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2685_ = lean_array_push(v_fst_2669_, v___x_2684_);
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_add(v_snd_2670_, v___x_2686_);
lean_dec(v_snd_2670_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2685_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v_a_2668_ = v___x_2688_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v_original_2696_, lean_object* v___x_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2696_, v___x_2697_, v_a_2698_, v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v___x_2697_);
lean_dec_ref(v_original_2696_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object* v_edited_2701_, lean_object* v___x_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_fst_2705_; lean_object* v_snd_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2731_; 
v_fst_2705_ = lean_ctor_get(v_a_2704_, 0);
v_snd_2706_ = lean_ctor_get(v_a_2704_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_a_2704_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2708_ = v_a_2704_;
v_isShared_2709_ = v_isSharedCheck_2731_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_snd_2706_);
lean_inc(v_fst_2705_);
lean_dec(v_a_2704_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2731_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; uint8_t v___y_2712_; uint8_t v___x_2727_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2727_ = lean_nat_dec_lt(v_snd_2706_, v___x_2702_);
if (v___x_2727_ == 0)
{
v___y_2712_ = v___x_2727_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = lean_array_get_borrowed(v___x_2710_, v_edited_2701_, v_snd_2706_);
v___x_2729_ = lean_string_dec_eq(v___x_2728_, v_a_2703_);
if (v___x_2729_ == 0)
{
v___y_2712_ = v___x_2727_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2730_; 
lean_del_object(v___x_2708_);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_fst_2705_);
lean_ctor_set(v___x_2730_, 1, v_snd_2706_);
return v___x_2730_;
}
}
v___jp_2711_:
{
if (v___y_2712_ == 0)
{
lean_object* v___x_2714_; 
if (v_isShared_2709_ == 0)
{
v___x_2714_ = v___x_2708_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_fst_2705_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_snd_2706_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
else
{
uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2716_ = 0;
v___x_2717_ = lean_array_get_borrowed(v___x_2710_, v_edited_2701_, v_snd_2706_);
v___x_2718_ = lean_box(v___x_2716_);
lean_inc(v___x_2717_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 1, v___x_2717_);
lean_ctor_set(v___x_2708_, 0, v___x_2718_);
v___x_2720_ = v___x_2708_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2717_);
v___x_2720_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2721_ = lean_array_push(v_fst_2705_, v___x_2720_);
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2723_ = lean_nat_add(v_snd_2706_, v___x_2722_);
lean_dec(v_snd_2706_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2721_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v_a_2704_ = v___x_2724_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object* v_edited_2732_, lean_object* v___x_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2732_, v___x_2733_, v_a_2734_, v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v___x_2733_);
lean_dec_ref(v_edited_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_original_2737_, lean_object* v___x_2738_, lean_object* v_edited_2739_, lean_object* v___x_2740_, lean_object* v_as_2741_, size_t v_sz_2742_, size_t v_i_2743_, lean_object* v_b_2744_){
_start:
{
uint8_t v___x_2745_; 
v___x_2745_ = lean_usize_dec_lt(v_i_2743_, v_sz_2742_);
if (v___x_2745_ == 0)
{
return v_b_2744_;
}
else
{
lean_object* v_snd_2746_; lean_object* v_fst_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2794_; 
v_snd_2746_ = lean_ctor_get(v_b_2744_, 1);
v_fst_2747_ = lean_ctor_get(v_b_2744_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_b_2744_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2749_ = v_b_2744_;
v_isShared_2750_ = v_isSharedCheck_2794_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_snd_2746_);
lean_inc(v_fst_2747_);
lean_dec(v_b_2744_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2794_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_fst_2751_; lean_object* v_snd_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2793_; 
v_fst_2751_ = lean_ctor_get(v_snd_2746_, 0);
v_snd_2752_ = lean_ctor_get(v_snd_2746_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_snd_2746_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2754_ = v_snd_2746_;
v_isShared_2755_ = v_isSharedCheck_2793_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_snd_2752_);
lean_inc(v_fst_2751_);
lean_dec(v_snd_2746_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2793_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_a_2756_; lean_object* v___x_2758_; 
v_a_2756_ = lean_array_uget_borrowed(v_as_2741_, v_i_2743_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v_fst_2751_);
lean_ctor_set(v___x_2754_, 0, v_fst_2747_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_fst_2747_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_fst_2751_);
v___x_2758_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v_fst_2760_; lean_object* v_snd_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2791_; 
v___x_2759_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2737_, v___x_2738_, v_a_2756_, v___x_2758_);
v_fst_2760_ = lean_ctor_get(v___x_2759_, 0);
v_snd_2761_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2763_ = v___x_2759_;
v_isShared_2764_ = v_isSharedCheck_2791_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_snd_2761_);
lean_inc(v_fst_2760_);
lean_dec(v___x_2759_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2791_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 1, v_snd_2752_);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_fst_2760_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_snd_2752_);
v___x_2766_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v_fst_2768_; lean_object* v_snd_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2789_; 
v___x_2767_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2739_, v___x_2740_, v_a_2756_, v___x_2766_);
v_fst_2768_ = lean_ctor_get(v___x_2767_, 0);
v_snd_2769_ = lean_ctor_get(v___x_2767_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2771_ = v___x_2767_;
v_isShared_2772_ = v_isSharedCheck_2789_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_snd_2769_);
lean_inc(v_fst_2768_);
lean_dec(v___x_2767_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2789_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2773_ = 2;
v___x_2774_ = lean_box(v___x_2773_);
lean_inc(v_a_2756_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v_a_2756_);
lean_ctor_set(v___x_2771_, 0, v___x_2774_);
v___x_2776_ = v___x_2771_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_a_2756_);
v___x_2776_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2777_ = lean_array_push(v_fst_2768_, v___x_2776_);
v___x_2778_ = lean_unsigned_to_nat(1u);
v___x_2779_ = lean_nat_add(v_snd_2761_, v___x_2778_);
lean_dec(v_snd_2761_);
v___x_2780_ = lean_nat_add(v_snd_2769_, v___x_2778_);
lean_dec(v_snd_2769_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v___x_2780_);
lean_ctor_set(v___x_2749_, 0, v___x_2779_);
v___x_2782_ = v___x_2749_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; 
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2777_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = ((size_t)1ULL);
v___x_2785_ = lean_usize_add(v_i_2743_, v___x_2784_);
v_i_2743_ = v___x_2785_;
v_b_2744_ = v___x_2783_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_original_2795_, lean_object* v___x_2796_, lean_object* v_edited_2797_, lean_object* v___x_2798_, lean_object* v_as_2799_, lean_object* v_sz_2800_, lean_object* v_i_2801_, lean_object* v_b_2802_){
_start:
{
size_t v_sz_boxed_2803_; size_t v_i_boxed_2804_; lean_object* v_res_2805_; 
v_sz_boxed_2803_ = lean_unbox_usize(v_sz_2800_);
lean_dec(v_sz_2800_);
v_i_boxed_2804_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2795_, v___x_2796_, v_edited_2797_, v___x_2798_, v_as_2799_, v_sz_boxed_2803_, v_i_boxed_2804_, v_b_2802_);
lean_dec_ref(v_as_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v_edited_2797_);
lean_dec(v___x_2796_);
lean_dec_ref(v_original_2795_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_2806_, lean_object* v___x_2807_, lean_object* v_original_2808_, lean_object* v___x_2809_, lean_object* v_as_2810_, size_t v_sz_2811_, size_t v_i_2812_, lean_object* v_b_2813_){
_start:
{
uint8_t v___x_2814_; 
v___x_2814_ = lean_usize_dec_lt(v_i_2812_, v_sz_2811_);
if (v___x_2814_ == 0)
{
return v_b_2813_;
}
else
{
lean_object* v_snd_2815_; lean_object* v_fst_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2863_; 
v_snd_2815_ = lean_ctor_get(v_b_2813_, 1);
v_fst_2816_ = lean_ctor_get(v_b_2813_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_b_2813_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2818_ = v_b_2813_;
v_isShared_2819_ = v_isSharedCheck_2863_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_snd_2815_);
lean_inc(v_fst_2816_);
lean_dec(v_b_2813_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2863_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2862_; 
v_fst_2820_ = lean_ctor_get(v_snd_2815_, 0);
v_snd_2821_ = lean_ctor_get(v_snd_2815_, 1);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_snd_2815_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2823_ = v_snd_2815_;
v_isShared_2824_ = v_isSharedCheck_2862_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snd_2821_);
lean_inc(v_fst_2820_);
lean_dec(v_snd_2815_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2862_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_a_2825_; lean_object* v___x_2827_; 
v_a_2825_ = lean_array_uget_borrowed(v_as_2810_, v_i_2812_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_fst_2820_);
lean_ctor_set(v___x_2823_, 0, v_fst_2816_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_fst_2816_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_fst_2820_);
v___x_2827_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v_fst_2829_; lean_object* v_snd_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2860_; 
v___x_2828_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2808_, v___x_2809_, v_a_2825_, v___x_2827_);
v_fst_2829_ = lean_ctor_get(v___x_2828_, 0);
v_snd_2830_ = lean_ctor_get(v___x_2828_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2832_ = v___x_2828_;
v_isShared_2833_ = v_isSharedCheck_2860_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_snd_2830_);
lean_inc(v_fst_2829_);
lean_dec(v___x_2828_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2860_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 1, v_snd_2821_);
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_fst_2829_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_snd_2821_);
v___x_2835_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v_fst_2837_; lean_object* v_snd_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2858_; 
v___x_2836_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2806_, v___x_2807_, v_a_2825_, v___x_2835_);
v_fst_2837_ = lean_ctor_get(v___x_2836_, 0);
v_snd_2838_ = lean_ctor_get(v___x_2836_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2840_ = v___x_2836_;
v_isShared_2841_ = v_isSharedCheck_2858_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_snd_2838_);
lean_inc(v_fst_2837_);
lean_dec(v___x_2836_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2858_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
uint8_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2842_ = 2;
v___x_2843_ = lean_box(v___x_2842_);
lean_inc(v_a_2825_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v_a_2825_);
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_a_2825_);
v___x_2845_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2846_ = lean_array_push(v_fst_2837_, v___x_2845_);
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = lean_nat_add(v_snd_2830_, v___x_2847_);
lean_dec(v_snd_2830_);
v___x_2849_ = lean_nat_add(v_snd_2838_, v___x_2847_);
lean_dec(v_snd_2838_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 1, v___x_2849_);
lean_ctor_set(v___x_2818_, 0, v___x_2848_);
v___x_2851_ = v___x_2818_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; lean_object* v___x_2855_; 
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2846_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = ((size_t)1ULL);
v___x_2854_ = lean_usize_add(v_i_2812_, v___x_2853_);
v___x_2855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2808_, v___x_2809_, v_edited_2806_, v___x_2807_, v_as_2810_, v_sz_2811_, v___x_2854_, v___x_2852_);
return v___x_2855_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_2864_, lean_object* v___x_2865_, lean_object* v_original_2866_, lean_object* v___x_2867_, lean_object* v_as_2868_, lean_object* v_sz_2869_, lean_object* v_i_2870_, lean_object* v_b_2871_){
_start:
{
size_t v_sz_boxed_2872_; size_t v_i_boxed_2873_; lean_object* v_res_2874_; 
v_sz_boxed_2872_ = lean_unbox_usize(v_sz_2869_);
lean_dec(v_sz_2869_);
v_i_boxed_2873_ = lean_unbox_usize(v_i_2870_);
lean_dec(v_i_2870_);
v_res_2874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_2864_, v___x_2865_, v_original_2866_, v___x_2867_, v_as_2868_, v_sz_boxed_2872_, v_i_boxed_2873_, v_b_2871_);
lean_dec_ref(v_as_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_original_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_edited_2864_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2875_, lean_object* v_x_2876_){
_start:
{
if (lean_obj_tag(v_x_2876_) == 0)
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_box(0);
return v___x_2877_;
}
else
{
lean_object* v_key_2878_; lean_object* v_value_2879_; lean_object* v_tail_2880_; uint8_t v___x_2881_; 
v_key_2878_ = lean_ctor_get(v_x_2876_, 0);
v_value_2879_ = lean_ctor_get(v_x_2876_, 1);
v_tail_2880_ = lean_ctor_get(v_x_2876_, 2);
v___x_2881_ = lean_string_dec_eq(v_key_2878_, v_a_2875_);
if (v___x_2881_ == 0)
{
v_x_2876_ = v_tail_2880_;
goto _start;
}
else
{
lean_object* v___x_2883_; 
lean_inc(v_value_2879_);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_value_2879_);
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2884_, lean_object* v_x_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2884_, v_x_2885_);
lean_dec(v_x_2885_);
lean_dec_ref(v_a_2884_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_buckets_2889_; lean_object* v___x_2890_; uint64_t v___x_2891_; uint64_t v___x_2892_; uint64_t v___x_2893_; uint64_t v_fold_2894_; uint64_t v___x_2895_; uint64_t v___x_2896_; uint64_t v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_buckets_2889_ = lean_ctor_get(v_m_2887_, 1);
v___x_2890_ = lean_array_get_size(v_buckets_2889_);
v___x_2891_ = lean_string_hash(v_a_2888_);
v___x_2892_ = 32ULL;
v___x_2893_ = lean_uint64_shift_right(v___x_2891_, v___x_2892_);
v_fold_2894_ = lean_uint64_xor(v___x_2891_, v___x_2893_);
v___x_2895_ = 16ULL;
v___x_2896_ = lean_uint64_shift_right(v_fold_2894_, v___x_2895_);
v___x_2897_ = lean_uint64_xor(v_fold_2894_, v___x_2896_);
v___x_2898_ = lean_uint64_to_usize(v___x_2897_);
v___x_2899_ = lean_usize_of_nat(v___x_2890_);
v___x_2900_ = ((size_t)1ULL);
v___x_2901_ = lean_usize_sub(v___x_2899_, v___x_2900_);
v___x_2902_ = lean_usize_land(v___x_2898_, v___x_2901_);
v___x_2903_ = lean_array_uget_borrowed(v_buckets_2889_, v___x_2902_);
v___x_2904_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2888_, v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2905_, v_a_2906_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_m_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2908_, lean_object* v_b_2909_, lean_object* v_x_2910_){
_start:
{
if (lean_obj_tag(v_x_2910_) == 0)
{
lean_dec(v_b_2909_);
lean_dec_ref(v_a_2908_);
return v_x_2910_;
}
else
{
lean_object* v_key_2911_; lean_object* v_value_2912_; lean_object* v_tail_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2925_; 
v_key_2911_ = lean_ctor_get(v_x_2910_, 0);
v_value_2912_ = lean_ctor_get(v_x_2910_, 1);
v_tail_2913_ = lean_ctor_get(v_x_2910_, 2);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_x_2910_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2915_ = v_x_2910_;
v_isShared_2916_ = v_isSharedCheck_2925_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_tail_2913_);
lean_inc(v_value_2912_);
lean_inc(v_key_2911_);
lean_dec(v_x_2910_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2925_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
uint8_t v___x_2917_; 
v___x_2917_ = lean_string_dec_eq(v_key_2911_, v_a_2908_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2908_, v_b_2909_, v_tail_2913_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 2, v___x_2918_);
v___x_2920_ = v___x_2915_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_key_2911_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_value_2912_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
else
{
lean_object* v___x_2923_; 
lean_dec(v_value_2912_);
lean_dec(v_key_2911_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v_b_2909_);
lean_ctor_set(v___x_2915_, 0, v_a_2908_);
v___x_2923_ = v___x_2915_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2908_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_b_2909_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_tail_2913_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2926_, lean_object* v_x_2927_){
_start:
{
if (lean_obj_tag(v_x_2927_) == 0)
{
uint8_t v___x_2928_; 
v___x_2928_ = 0;
return v___x_2928_;
}
else
{
lean_object* v_key_2929_; lean_object* v_tail_2930_; uint8_t v___x_2931_; 
v_key_2929_ = lean_ctor_get(v_x_2927_, 0);
v_tail_2930_ = lean_ctor_get(v_x_2927_, 2);
v___x_2931_ = lean_string_dec_eq(v_key_2929_, v_a_2926_);
if (v___x_2931_ == 0)
{
v_x_2927_ = v_tail_2930_;
goto _start;
}
else
{
return v___x_2931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2933_, lean_object* v_x_2934_){
_start:
{
uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_res_2935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2933_, v_x_2934_);
lean_dec(v_x_2934_);
lean_dec_ref(v_a_2933_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
if (lean_obj_tag(v_x_2938_) == 0)
{
return v_x_2937_;
}
else
{
lean_object* v_key_2939_; lean_object* v_value_2940_; lean_object* v_tail_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2964_; 
v_key_2939_ = lean_ctor_get(v_x_2938_, 0);
v_value_2940_ = lean_ctor_get(v_x_2938_, 1);
v_tail_2941_ = lean_ctor_get(v_x_2938_, 2);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_x_2938_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2943_ = v_x_2938_;
v_isShared_2944_ = v_isSharedCheck_2964_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_tail_2941_);
lean_inc(v_value_2940_);
lean_inc(v_key_2939_);
lean_dec(v_x_2938_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2964_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; uint64_t v___x_2948_; uint64_t v_fold_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2945_ = lean_array_get_size(v_x_2937_);
v___x_2946_ = lean_string_hash(v_key_2939_);
v___x_2947_ = 32ULL;
v___x_2948_ = lean_uint64_shift_right(v___x_2946_, v___x_2947_);
v_fold_2949_ = lean_uint64_xor(v___x_2946_, v___x_2948_);
v___x_2950_ = 16ULL;
v___x_2951_ = lean_uint64_shift_right(v_fold_2949_, v___x_2950_);
v___x_2952_ = lean_uint64_xor(v_fold_2949_, v___x_2951_);
v___x_2953_ = lean_uint64_to_usize(v___x_2952_);
v___x_2954_ = lean_usize_of_nat(v___x_2945_);
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_sub(v___x_2954_, v___x_2955_);
v___x_2957_ = lean_usize_land(v___x_2953_, v___x_2956_);
v___x_2958_ = lean_array_uget_borrowed(v_x_2937_, v___x_2957_);
lean_inc(v___x_2958_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 2, v___x_2958_);
v___x_2960_ = v___x_2943_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_key_2939_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_value_2940_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_array_uset(v_x_2937_, v___x_2957_, v___x_2960_);
v_x_2937_ = v___x_2961_;
v_x_2938_ = v_tail_2941_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2965_, lean_object* v_source_2966_, lean_object* v_target_2967_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_array_get_size(v_source_2966_);
v___x_2969_ = lean_nat_dec_lt(v_i_2965_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec_ref(v_source_2966_);
lean_dec(v_i_2965_);
return v_target_2967_;
}
else
{
lean_object* v_es_2970_; lean_object* v___x_2971_; lean_object* v_source_2972_; lean_object* v_target_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_es_2970_ = lean_array_fget(v_source_2966_, v_i_2965_);
v___x_2971_ = lean_box(0);
v_source_2972_ = lean_array_fset(v_source_2966_, v_i_2965_, v___x_2971_);
v_target_2973_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2967_, v_es_2970_);
v___x_2974_ = lean_unsigned_to_nat(1u);
v___x_2975_ = lean_nat_add(v_i_2965_, v___x_2974_);
lean_dec(v_i_2965_);
v_i_2965_ = v___x_2975_;
v_source_2966_ = v_source_2972_;
v_target_2967_ = v_target_2973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2977_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v_nbuckets_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2978_ = lean_array_get_size(v_data_2977_);
v___x_2979_ = lean_unsigned_to_nat(2u);
v_nbuckets_2980_ = lean_nat_mul(v___x_2978_, v___x_2979_);
v___x_2981_ = lean_unsigned_to_nat(0u);
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_mk_array(v_nbuckets_2980_, v___x_2982_);
v___x_2984_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2981_, v_data_2977_, v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2985_, lean_object* v_a_2986_, lean_object* v_b_2987_){
_start:
{
lean_object* v_size_2988_; lean_object* v_buckets_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3032_; 
v_size_2988_ = lean_ctor_get(v_m_2985_, 0);
v_buckets_2989_ = lean_ctor_get(v_m_2985_, 1);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_m_2985_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_2991_ = v_m_2985_;
v_isShared_2992_ = v_isSharedCheck_3032_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_buckets_2989_);
lean_inc(v_size_2988_);
lean_dec(v_m_2985_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3032_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; uint64_t v___x_2994_; uint64_t v___x_2995_; uint64_t v___x_2996_; uint64_t v_fold_2997_; uint64_t v___x_2998_; uint64_t v___x_2999_; uint64_t v___x_3000_; size_t v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; size_t v___x_3004_; size_t v___x_3005_; lean_object* v_bkt_3006_; uint8_t v___x_3007_; 
v___x_2993_ = lean_array_get_size(v_buckets_2989_);
v___x_2994_ = lean_string_hash(v_a_2986_);
v___x_2995_ = 32ULL;
v___x_2996_ = lean_uint64_shift_right(v___x_2994_, v___x_2995_);
v_fold_2997_ = lean_uint64_xor(v___x_2994_, v___x_2996_);
v___x_2998_ = 16ULL;
v___x_2999_ = lean_uint64_shift_right(v_fold_2997_, v___x_2998_);
v___x_3000_ = lean_uint64_xor(v_fold_2997_, v___x_2999_);
v___x_3001_ = lean_uint64_to_usize(v___x_3000_);
v___x_3002_ = lean_usize_of_nat(v___x_2993_);
v___x_3003_ = ((size_t)1ULL);
v___x_3004_ = lean_usize_sub(v___x_3002_, v___x_3003_);
v___x_3005_ = lean_usize_land(v___x_3001_, v___x_3004_);
v_bkt_3006_ = lean_array_uget_borrowed(v_buckets_2989_, v___x_3005_);
v___x_3007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2986_, v_bkt_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v_size_x27_3009_; lean_object* v___x_3010_; lean_object* v_buckets_x27_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3008_ = lean_unsigned_to_nat(1u);
v_size_x27_3009_ = lean_nat_add(v_size_2988_, v___x_3008_);
lean_dec(v_size_2988_);
lean_inc(v_bkt_3006_);
v___x_3010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3010_, 0, v_a_2986_);
lean_ctor_set(v___x_3010_, 1, v_b_2987_);
lean_ctor_set(v___x_3010_, 2, v_bkt_3006_);
v_buckets_x27_3011_ = lean_array_uset(v_buckets_2989_, v___x_3005_, v___x_3010_);
v___x_3012_ = lean_unsigned_to_nat(4u);
v___x_3013_ = lean_nat_mul(v_size_x27_3009_, v___x_3012_);
v___x_3014_ = lean_unsigned_to_nat(3u);
v___x_3015_ = lean_nat_div(v___x_3013_, v___x_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_array_get_size(v_buckets_x27_3011_);
v___x_3017_ = lean_nat_dec_le(v___x_3015_, v___x_3016_);
lean_dec(v___x_3015_);
if (v___x_3017_ == 0)
{
lean_object* v_val_3018_; lean_object* v___x_3020_; 
v_val_3018_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_3011_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v_val_3018_);
lean_ctor_set(v___x_2991_, 0, v_size_x27_3009_);
v___x_3020_ = v___x_2991_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_size_x27_3009_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_val_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
else
{
lean_object* v___x_3023_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v_buckets_x27_3011_);
lean_ctor_set(v___x_2991_, 0, v_size_x27_3009_);
v___x_3023_ = v___x_2991_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_size_x27_3009_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_buckets_x27_3011_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_object* v___x_3025_; lean_object* v_buckets_x27_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
lean_inc(v_bkt_3006_);
v___x_3025_ = lean_box(0);
v_buckets_x27_3026_ = lean_array_uset(v_buckets_2989_, v___x_3005_, v___x_3025_);
v___x_3027_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2986_, v_b_2987_, v_bkt_3006_);
v___x_3028_ = lean_array_uset(v_buckets_x27_3026_, v___x_3005_, v___x_3027_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_3028_);
v___x_3030_ = v___x_2991_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_size_2988_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_3033_, lean_object* v_index_3034_, lean_object* v_val_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3033_, v_val_3035_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_index_3034_);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3037_);
lean_ctor_set(v___x_3041_, 1, v___x_3038_);
lean_ctor_set(v___x_3041_, 2, v___x_3039_);
lean_ctor_set(v___x_3041_, 3, v___x_3040_);
v___x_3042_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3033_, v_val_3035_, v___x_3041_);
return v___x_3042_;
}
else
{
lean_object* v_val_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3064_; 
v_val_3043_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3045_ = v___x_3036_;
v_isShared_3046_ = v_isSharedCheck_3064_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_val_3043_);
lean_dec(v___x_3036_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3064_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_leftCount_3047_; lean_object* v_rightCount_3048_; lean_object* v_rightIndex_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3062_; 
v_leftCount_3047_ = lean_ctor_get(v_val_3043_, 0);
v_rightCount_3048_ = lean_ctor_get(v_val_3043_, 2);
v_rightIndex_3049_ = lean_ctor_get(v_val_3043_, 3);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_val_3043_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_val_3043_, 1);
lean_dec(v_unused_3063_);
v___x_3051_ = v_val_3043_;
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_rightIndex_3049_);
lean_inc(v_rightCount_3048_);
lean_inc(v_leftCount_3047_);
lean_dec(v_val_3043_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3053_ = lean_unsigned_to_nat(1u);
v___x_3054_ = lean_nat_add(v_leftCount_3047_, v___x_3053_);
lean_dec(v_leftCount_3047_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v_index_3034_);
v___x_3056_ = v___x_3045_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_index_3034_);
v___x_3056_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3058_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v___x_3056_);
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3058_ = v___x_3051_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_rightCount_3048_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_rightIndex_3049_);
v___x_3058_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3033_, v_val_3035_, v___x_3058_);
return v___x_3059_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3065_, lean_object* v_fst_3066_, lean_object* v___x_3067_, lean_object* v_fst_3068_, lean_object* v_a_3069_, lean_object* v_b_3070_){
_start:
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_nat_dec_lt(v_a_3069_, v_upperBound_3065_);
if (v___x_3071_ == 0)
{
lean_dec(v_a_3069_);
return v_b_3070_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = l_Subarray_get___redArg(v_fst_3068_, v_a_3069_);
lean_inc(v_a_3069_);
v___x_3073_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3070_, v_a_3069_, v___x_3072_);
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_nat_add(v_a_3069_, v___x_3074_);
lean_dec(v_a_3069_);
v_a_3069_ = v___x_3075_;
v_b_3070_ = v___x_3073_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3077_, lean_object* v_fst_3078_, lean_object* v___x_3079_, lean_object* v_fst_3080_, lean_object* v_a_3081_, lean_object* v_b_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3077_, v_fst_3078_, v___x_3079_, v_fst_3080_, v_a_3081_, v_b_3082_);
lean_dec_ref(v_fst_3080_);
lean_dec(v___x_3079_);
lean_dec_ref(v_fst_3078_);
lean_dec(v_upperBound_3077_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3084_, lean_object* v_x_3085_){
_start:
{
if (lean_obj_tag(v_x_3085_) == 0)
{
lean_inc(v_x_3084_);
return v_x_3084_;
}
else
{
lean_object* v_key_3086_; lean_object* v_value_3087_; lean_object* v_tail_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_key_3086_ = lean_ctor_get(v_x_3085_, 0);
v_value_3087_ = lean_ctor_get(v_x_3085_, 1);
v_tail_3088_ = lean_ctor_get(v_x_3085_, 2);
v___x_3089_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3084_, v_tail_3088_);
lean_inc(v_value_3087_);
lean_inc(v_key_3086_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v_key_3086_);
lean_ctor_set(v___x_3090_, 1, v_value_3087_);
v___x_3091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3089_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3092_, v_x_3093_);
lean_dec(v_x_3093_);
lean_dec(v_x_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3095_, size_t v_i_3096_, size_t v_stop_3097_, lean_object* v_b_3098_){
_start:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_eq(v_i_3096_, v_stop_3097_);
if (v___x_3099_ == 0)
{
size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_sub(v_i_3096_, v___x_3100_);
v___x_3102_ = lean_array_uget_borrowed(v_as_3095_, v___x_3101_);
v___x_3103_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3098_, v___x_3102_);
lean_dec(v_b_3098_);
v_i_3096_ = v___x_3101_;
v_b_3098_ = v___x_3103_;
goto _start;
}
else
{
return v_b_3098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3105_, lean_object* v_i_3106_, lean_object* v_stop_3107_, lean_object* v_b_3108_){
_start:
{
size_t v_i_boxed_3109_; size_t v_stop_boxed_3110_; lean_object* v_res_3111_; 
v_i_boxed_3109_ = lean_unbox_usize(v_i_3106_);
lean_dec(v_i_3106_);
v_stop_boxed_3110_ = lean_unbox_usize(v_stop_3107_);
lean_dec(v_stop_3107_);
v_res_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3105_, v_i_boxed_3109_, v_stop_boxed_3110_, v_b_3108_);
lean_dec_ref(v_as_3105_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3112_, lean_object* v_right_3113_, lean_object* v_pref_3114_){
_start:
{
lean_object* v_start_3115_; lean_object* v_stop_3116_; lean_object* v_i_3117_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_start_3115_ = lean_ctor_get(v_left_3112_, 1);
v_stop_3116_ = lean_ctor_get(v_left_3112_, 2);
v_i_3117_ = lean_array_get_size(v_pref_3114_);
v___x_3123_ = lean_nat_sub(v_stop_3116_, v_start_3115_);
v___x_3124_ = lean_nat_dec_lt(v_i_3117_, v___x_3123_);
lean_dec(v___x_3123_);
if (v___x_3124_ == 0)
{
goto v___jp_3118_;
}
else
{
lean_object* v_start_3125_; lean_object* v_stop_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v_start_3125_ = lean_ctor_get(v_right_3113_, 1);
v_stop_3126_ = lean_ctor_get(v_right_3113_, 2);
v___x_3127_ = lean_nat_sub(v_stop_3126_, v_start_3125_);
v___x_3128_ = lean_nat_dec_lt(v_i_3117_, v___x_3127_);
lean_dec(v___x_3127_);
if (v___x_3128_ == 0)
{
goto v___jp_3118_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = l_Subarray_get___redArg(v_left_3112_, v_i_3117_);
v___x_3130_ = l_Subarray_get___redArg(v_right_3113_, v_i_3117_);
v___x_3131_ = lean_string_dec_eq(v___x_3129_, v___x_3130_);
lean_dec(v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v___x_3129_);
v___x_3132_ = l_Subarray_drop___redArg(v_left_3112_, v_i_3117_);
v___x_3133_ = l_Subarray_drop___redArg(v_right_3113_, v_i_3117_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_pref_3114_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_array_push(v_pref_3114_, v___x_3129_);
v_pref_3114_ = v___x_3136_;
goto _start;
}
}
}
v___jp_3118_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3119_ = l_Subarray_drop___redArg(v_left_3112_, v_i_3117_);
v___x_3120_ = l_Subarray_drop___redArg(v_right_3113_, v_i_3117_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v_pref_3114_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
return v___x_3122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3140_, lean_object* v_right_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3143_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3140_, v_right_3141_, v___x_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3144_, lean_object* v_b_3145_){
_start:
{
lean_object* v_array_3146_; lean_object* v_start_3147_; lean_object* v_stop_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3161_; 
v_array_3146_ = lean_ctor_get(v_a_3144_, 0);
v_start_3147_ = lean_ctor_get(v_a_3144_, 1);
v_stop_3148_ = lean_ctor_get(v_a_3144_, 2);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3144_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3150_ = v_a_3144_;
v_isShared_3151_ = v_isSharedCheck_3161_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_stop_3148_);
lean_inc(v_start_3147_);
lean_inc(v_array_3146_);
lean_dec(v_a_3144_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3161_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_nat_dec_lt(v_start_3147_, v_stop_3148_);
if (v___x_3152_ == 0)
{
lean_del_object(v___x_3150_);
lean_dec(v_stop_3148_);
lean_dec(v_start_3147_);
lean_dec_ref(v_array_3146_);
return v_b_3145_;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v_start_3147_, v___x_3153_);
lean_inc_ref(v_array_3146_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v___x_3154_);
v___x_3156_ = v___x_3150_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_array_3146_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_stop_3148_);
v___x_3156_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_array_fget(v_array_3146_, v_start_3147_);
lean_dec(v_start_3147_);
lean_dec_ref(v_array_3146_);
v___x_3158_ = lean_array_push(v_b_3145_, v___x_3157_);
v_a_3144_ = v___x_3156_;
v_b_3145_ = v___x_3158_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3162_, lean_object* v_right_3163_, lean_object* v_i_3164_){
_start:
{
lean_object* v_start_3165_; lean_object* v_stop_3166_; lean_object* v___x_3167_; uint8_t v___x_3181_; 
v_start_3165_ = lean_ctor_get(v_left_3162_, 1);
v_stop_3166_ = lean_ctor_get(v_left_3162_, 2);
v___x_3167_ = lean_nat_sub(v_stop_3166_, v_start_3165_);
v___x_3181_ = lean_nat_dec_lt(v_i_3164_, v___x_3167_);
if (v___x_3181_ == 0)
{
goto v___jp_3168_;
}
else
{
lean_object* v_start_3182_; lean_object* v_stop_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v_start_3182_ = lean_ctor_get(v_right_3163_, 1);
v_stop_3183_ = lean_ctor_get(v_right_3163_, 2);
v___x_3184_ = lean_nat_sub(v_stop_3183_, v_start_3182_);
v___x_3185_ = lean_nat_dec_lt(v_i_3164_, v___x_3184_);
if (v___x_3185_ == 0)
{
lean_dec(v___x_3184_);
goto v___jp_3168_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3186_ = lean_nat_sub(v___x_3167_, v_i_3164_);
lean_dec(v___x_3167_);
v___x_3187_ = lean_unsigned_to_nat(1u);
v___x_3188_ = lean_nat_sub(v___x_3186_, v___x_3187_);
v___x_3189_ = l_Subarray_get___redArg(v_left_3162_, v___x_3188_);
lean_dec(v___x_3188_);
v___x_3190_ = lean_nat_sub(v___x_3184_, v_i_3164_);
lean_dec(v___x_3184_);
v___x_3191_ = lean_nat_sub(v___x_3190_, v___x_3187_);
v___x_3192_ = l_Subarray_get___redArg(v_right_3163_, v___x_3191_);
lean_dec(v___x_3191_);
v___x_3193_ = lean_string_dec_eq(v___x_3189_, v___x_3192_);
lean_dec(v___x_3192_);
lean_dec(v___x_3189_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_dec(v_i_3164_);
lean_inc_ref(v_left_3162_);
v___x_3194_ = l_Subarray_take___redArg(v_left_3162_, v___x_3186_);
v___x_3195_ = l_Subarray_take___redArg(v_right_3163_, v___x_3190_);
lean_dec(v___x_3190_);
v___x_3196_ = l_Subarray_drop___redArg(v_left_3162_, v___x_3186_);
lean_dec(v___x_3186_);
v___x_3197_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3198_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3196_, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3195_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3194_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; 
lean_dec(v___x_3190_);
lean_dec(v___x_3186_);
v___x_3201_ = lean_nat_add(v_i_3164_, v___x_3187_);
lean_dec(v_i_3164_);
v_i_3164_ = v___x_3201_;
goto _start;
}
}
}
v___jp_3168_:
{
lean_object* v_start_3169_; lean_object* v_stop_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_start_3169_ = lean_ctor_get(v_right_3163_, 1);
v_stop_3170_ = lean_ctor_get(v_right_3163_, 2);
v___x_3171_ = lean_nat_sub(v___x_3167_, v_i_3164_);
lean_dec(v___x_3167_);
lean_inc_ref(v_left_3162_);
v___x_3172_ = l_Subarray_take___redArg(v_left_3162_, v___x_3171_);
v___x_3173_ = lean_nat_sub(v_stop_3170_, v_start_3169_);
v___x_3174_ = lean_nat_sub(v___x_3173_, v_i_3164_);
lean_dec(v_i_3164_);
lean_dec(v___x_3173_);
v___x_3175_ = l_Subarray_take___redArg(v_right_3163_, v___x_3174_);
lean_dec(v___x_3174_);
v___x_3176_ = l_Subarray_drop___redArg(v_left_3162_, v___x_3171_);
lean_dec(v___x_3171_);
v___x_3177_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3178_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3176_, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3175_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3172_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3203_, lean_object* v_right_3204_){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3203_, v_right_3204_, v___x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3207_, lean_object* v_b_3208_){
_start:
{
if (lean_obj_tag(v_as_x27_3207_) == 0)
{
return v_b_3208_;
}
else
{
lean_object* v_head_3209_; lean_object* v_snd_3210_; lean_object* v_leftIndex_3211_; 
v_head_3209_ = lean_ctor_get(v_as_x27_3207_, 0);
v_snd_3210_ = lean_ctor_get(v_head_3209_, 1);
v_leftIndex_3211_ = lean_ctor_get(v_snd_3210_, 1);
if (lean_obj_tag(v_leftIndex_3211_) == 1)
{
lean_object* v_rightIndex_3212_; 
v_rightIndex_3212_ = lean_ctor_get(v_snd_3210_, 3);
if (lean_obj_tag(v_rightIndex_3212_) == 1)
{
if (lean_obj_tag(v_b_3208_) == 0)
{
lean_object* v_tail_3213_; lean_object* v_fst_3214_; lean_object* v_leftCount_3215_; lean_object* v_rightCount_3216_; lean_object* v_val_3217_; lean_object* v_val_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_tail_3213_ = lean_ctor_get(v_as_x27_3207_, 1);
v_fst_3214_ = lean_ctor_get(v_head_3209_, 0);
v_leftCount_3215_ = lean_ctor_get(v_snd_3210_, 0);
v_rightCount_3216_ = lean_ctor_get(v_snd_3210_, 2);
v_val_3217_ = lean_ctor_get(v_leftIndex_3211_, 0);
v_val_3218_ = lean_ctor_get(v_rightIndex_3212_, 0);
v___x_3219_ = lean_nat_add(v_leftCount_3215_, v_rightCount_3216_);
lean_inc(v_val_3218_);
lean_inc(v_val_3217_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_val_3217_);
lean_ctor_set(v___x_3220_, 1, v_val_3218_);
lean_inc(v_fst_3214_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_fst_3214_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3219_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v_as_x27_3207_ = v_tail_3213_;
v_b_3208_ = v___x_3223_;
goto _start;
}
else
{
lean_object* v_val_3225_; lean_object* v_tail_3226_; lean_object* v_fst_3227_; lean_object* v_leftCount_3228_; lean_object* v_rightCount_3229_; lean_object* v_val_3230_; lean_object* v_val_3231_; lean_object* v_fst_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3253_; 
v_val_3225_ = lean_ctor_get(v_b_3208_, 0);
lean_inc(v_val_3225_);
v_tail_3226_ = lean_ctor_get(v_as_x27_3207_, 1);
v_fst_3227_ = lean_ctor_get(v_head_3209_, 0);
v_leftCount_3228_ = lean_ctor_get(v_snd_3210_, 0);
v_rightCount_3229_ = lean_ctor_get(v_snd_3210_, 2);
v_val_3230_ = lean_ctor_get(v_leftIndex_3211_, 0);
v_val_3231_ = lean_ctor_get(v_rightIndex_3212_, 0);
v_fst_3232_ = lean_ctor_get(v_val_3225_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_val_3225_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v_val_3225_, 1);
lean_dec(v_unused_3254_);
v___x_3234_ = v_val_3225_;
v_isShared_3235_ = v_isSharedCheck_3253_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_fst_3232_);
lean_dec(v_val_3225_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3253_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3236_ = lean_nat_add(v_leftCount_3228_, v_rightCount_3229_);
v___x_3237_ = lean_nat_dec_lt(v___x_3236_, v_fst_3232_);
lean_dec(v_fst_3232_);
if (v___x_3237_ == 0)
{
lean_dec(v___x_3236_);
lean_del_object(v___x_3234_);
v_as_x27_3207_ = v_tail_3226_;
goto _start;
}
else
{
lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3251_; 
v_isSharedCheck_3251_ = !lean_is_exclusive(v_b_3208_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v_b_3208_, 0);
lean_dec(v_unused_3252_);
v___x_3240_ = v_b_3208_;
v_isShared_3241_ = v_isSharedCheck_3251_;
goto v_resetjp_3239_;
}
else
{
lean_dec(v_b_3208_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3251_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
lean_inc(v_val_3231_);
lean_inc(v_val_3230_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 1, v_val_3231_);
lean_ctor_set(v___x_3234_, 0, v_val_3230_);
v___x_3243_ = v___x_3234_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_val_3230_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_val_3231_);
v___x_3243_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_inc(v_fst_3227_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_fst_3227_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3236_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3245_);
v___x_3247_ = v___x_3240_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
v_as_x27_3207_ = v_tail_3226_;
v_b_3208_ = v___x_3247_;
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
lean_object* v_tail_3255_; 
v_tail_3255_ = lean_ctor_get(v_as_x27_3207_, 1);
v_as_x27_3207_ = v_tail_3255_;
goto _start;
}
}
else
{
lean_object* v_tail_3257_; 
v_tail_3257_ = lean_ctor_get(v_as_x27_3207_, 1);
v_as_x27_3207_ = v_tail_3257_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_as_x27_3259_, lean_object* v_b_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3259_, v_b_3260_);
lean_dec(v_as_x27_3259_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3262_, lean_object* v_index_3263_, lean_object* v_val_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3262_, v_val_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_unsigned_to_nat(1u);
v___x_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3269_, 0, v_index_3263_);
v___x_3270_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3266_);
lean_ctor_set(v___x_3270_, 1, v___x_3267_);
lean_ctor_set(v___x_3270_, 2, v___x_3268_);
lean_ctor_set(v___x_3270_, 3, v___x_3269_);
v___x_3271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3262_, v_val_3264_, v___x_3270_);
return v___x_3271_;
}
else
{
lean_object* v_val_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3293_; 
v_val_3272_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3274_ = v___x_3265_;
v_isShared_3275_ = v_isSharedCheck_3293_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_val_3272_);
lean_dec(v___x_3265_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3293_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_leftCount_3276_; lean_object* v_leftIndex_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3290_; 
v_leftCount_3276_ = lean_ctor_get(v_val_3272_, 0);
v_leftIndex_3277_ = lean_ctor_get(v_val_3272_, 1);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_val_3272_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; lean_object* v_unused_3292_; 
v_unused_3291_ = lean_ctor_get(v_val_3272_, 3);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_val_3272_, 2);
lean_dec(v_unused_3292_);
v___x_3279_ = v_val_3272_;
v_isShared_3280_ = v_isSharedCheck_3290_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_leftIndex_3277_);
lean_inc(v_leftCount_3276_);
lean_dec(v_val_3272_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3290_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_nat_add(v_leftCount_3276_, v___x_3281_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_index_3263_);
v___x_3284_ = v___x_3274_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_index_3263_);
v___x_3284_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3286_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 3, v___x_3284_);
lean_ctor_set(v___x_3279_, 2, v___x_3282_);
v___x_3286_ = v___x_3279_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_leftCount_3276_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_leftIndex_3277_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3288_, 3, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3262_, v_val_3264_, v___x_3286_);
return v___x_3287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3294_, lean_object* v___x_3295_, lean_object* v_fst_3296_, lean_object* v___x_3297_, lean_object* v_a_3298_, lean_object* v_b_3299_){
_start:
{
uint8_t v___x_3300_; 
v___x_3300_ = lean_nat_dec_lt(v_a_3298_, v_upperBound_3294_);
if (v___x_3300_ == 0)
{
lean_dec(v_a_3298_);
return v_b_3299_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3301_ = l_Subarray_get___redArg(v_fst_3296_, v_a_3298_);
lean_inc(v_a_3298_);
v___x_3302_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3299_, v_a_3298_, v___x_3301_);
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = lean_nat_add(v_a_3298_, v___x_3303_);
lean_dec(v_a_3298_);
v_a_3298_ = v___x_3304_;
v_b_3299_ = v___x_3302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3306_, lean_object* v___x_3307_, lean_object* v_fst_3308_, lean_object* v___x_3309_, lean_object* v_a_3310_, lean_object* v_b_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3306_, v___x_3307_, v_fst_3308_, v___x_3309_, v_a_3310_, v_b_3311_);
lean_dec(v___x_3309_);
lean_dec_ref(v_fst_3308_);
lean_dec(v___x_3307_);
lean_dec(v_upperBound_3306_);
return v_res_3312_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_box(0);
v___x_3314_ = lean_unsigned_to_nat(16u);
v___x_3315_ = lean_mk_array(v___x_3314_, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_hist_3318_; 
v___x_3316_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3317_ = lean_unsigned_to_nat(0u);
v_hist_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3318_, 0, v___x_3317_);
lean_ctor_set(v_hist_3318_, 1, v___x_3316_);
return v_hist_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3319_, lean_object* v_right_3320_){
_start:
{
lean_object* v___x_3321_; lean_object* v_snd_3322_; lean_object* v_fst_3323_; lean_object* v_fst_3324_; lean_object* v_snd_3325_; lean_object* v___x_3326_; lean_object* v_snd_3327_; lean_object* v_fst_3328_; lean_object* v_fst_3329_; lean_object* v_snd_3330_; lean_object* v_start_3331_; lean_object* v_stop_3332_; lean_object* v___x_3333_; lean_object* v_hist_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_start_3337_; lean_object* v_stop_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v_buckets_3341_; lean_object* v___x_3342_; lean_object* v___y_3344_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3321_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3319_, v_right_3320_);
v_snd_3322_ = lean_ctor_get(v___x_3321_, 1);
lean_inc(v_snd_3322_);
v_fst_3323_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_fst_3323_);
lean_dec_ref(v___x_3321_);
v_fst_3324_ = lean_ctor_get(v_snd_3322_, 0);
lean_inc(v_fst_3324_);
v_snd_3325_ = lean_ctor_get(v_snd_3322_, 1);
lean_inc(v_snd_3325_);
lean_dec(v_snd_3322_);
v___x_3326_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3324_, v_snd_3325_);
v_snd_3327_ = lean_ctor_get(v___x_3326_, 1);
lean_inc(v_snd_3327_);
v_fst_3328_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_fst_3328_);
lean_dec_ref(v___x_3326_);
v_fst_3329_ = lean_ctor_get(v_snd_3327_, 0);
lean_inc(v_fst_3329_);
v_snd_3330_ = lean_ctor_get(v_snd_3327_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_snd_3327_);
v_start_3331_ = lean_ctor_get(v_fst_3328_, 1);
v_stop_3332_ = lean_ctor_get(v_fst_3328_, 2);
v___x_3333_ = lean_unsigned_to_nat(0u);
v_hist_3334_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3335_ = lean_nat_sub(v_stop_3332_, v_start_3331_);
v___x_3336_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3335_, v_fst_3329_, v___x_3335_, v_fst_3328_, v___x_3333_, v_hist_3334_);
v_start_3337_ = lean_ctor_get(v_fst_3329_, 1);
v_stop_3338_ = lean_ctor_get(v_fst_3329_, 2);
v___x_3339_ = lean_nat_sub(v_stop_3338_, v_start_3337_);
v___x_3340_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3339_, v___x_3339_, v_fst_3329_, v___x_3335_, v___x_3333_, v___x_3336_);
lean_dec(v___x_3335_);
lean_dec(v___x_3339_);
v_buckets_3341_ = lean_ctor_get(v___x_3340_, 1);
lean_inc_ref(v_buckets_3341_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = lean_box(0);
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_array_get_size(v_buckets_3341_);
v___x_3372_ = lean_nat_dec_lt(v___x_3333_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_dec_ref(v_buckets_3341_);
v___y_3344_ = v___x_3370_;
goto v___jp_3343_;
}
else
{
size_t v___x_3373_; size_t v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = lean_usize_of_nat(v___x_3371_);
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3341_, v___x_3373_, v___x_3374_, v___x_3370_);
lean_dec_ref(v_buckets_3341_);
v___y_3344_ = v___x_3375_;
goto v___jp_3343_;
}
v___jp_3343_:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3344_, v___x_3342_);
lean_dec(v___y_3344_);
if (lean_obj_tag(v___x_3345_) == 1)
{
lean_object* v_val_3346_; lean_object* v_snd_3347_; lean_object* v_snd_3348_; lean_object* v_fst_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3352_; lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3355_; lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v_val_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_val_3346_);
lean_dec_ref(v___x_3345_);
v_snd_3347_ = lean_ctor_get(v_val_3346_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_val_3346_);
v_snd_3348_ = lean_ctor_get(v_snd_3347_, 1);
lean_inc(v_snd_3348_);
v_fst_3349_ = lean_ctor_get(v_snd_3347_, 0);
lean_inc(v_fst_3349_);
lean_dec(v_snd_3347_);
v_fst_3350_ = lean_ctor_get(v_snd_3348_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v_snd_3348_, 1);
lean_inc(v_snd_3351_);
lean_dec(v_snd_3348_);
v___x_3352_ = l_Subarray_split___redArg(v_fst_3328_, v_fst_3350_);
lean_dec(v_fst_3350_);
v_fst_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_fst_3353_);
v_snd_3354_ = lean_ctor_get(v___x_3352_, 1);
lean_inc(v_snd_3354_);
lean_dec_ref(v___x_3352_);
v___x_3355_ = l_Subarray_split___redArg(v_fst_3329_, v_snd_3351_);
lean_dec(v_snd_3351_);
v_fst_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_fst_3356_);
v_snd_3357_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_snd_3357_);
lean_dec_ref(v___x_3355_);
v___x_3358_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3353_, v_fst_3356_);
v___x_3359_ = l_Array_append___redArg(v_fst_3323_, v___x_3358_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = lean_mk_empty_array_with_capacity(v___x_3360_);
v___x_3362_ = lean_array_push(v___x_3361_, v_fst_3349_);
v___x_3363_ = l_Array_append___redArg(v___x_3359_, v___x_3362_);
lean_dec_ref(v___x_3362_);
v___x_3364_ = l_Subarray_drop___redArg(v_snd_3354_, v___x_3360_);
v___x_3365_ = l_Subarray_drop___redArg(v_snd_3357_, v___x_3360_);
v___x_3366_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3364_, v___x_3365_);
v___x_3367_ = l_Array_append___redArg(v___x_3363_, v___x_3366_);
lean_dec_ref(v___x_3366_);
v___x_3368_ = l_Array_append___redArg(v___x_3367_, v_snd_3330_);
lean_dec(v_snd_3330_);
return v___x_3368_;
}
else
{
lean_object* v___x_3369_; 
lean_dec(v___x_3345_);
lean_dec(v_fst_3329_);
lean_dec(v_fst_3328_);
v___x_3369_ = l_Array_append___redArg(v_fst_3323_, v_snd_3330_);
lean_dec(v_snd_3330_);
return v___x_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_3376_, lean_object* v_edited_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3399_; 
v_fst_3379_ = lean_ctor_get(v_a_3378_, 0);
v_snd_3380_ = lean_ctor_get(v_a_3378_, 1);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_a_3378_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3382_ = v_a_3378_;
v_isShared_3383_ = v_isSharedCheck_3399_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_snd_3380_);
lean_inc(v_fst_3379_);
lean_dec(v_a_3378_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3399_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_nat_dec_lt(v_snd_3380_, v___x_3376_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3386_; 
if (v_isShared_3383_ == 0)
{
v___x_3386_ = v___x_3382_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_fst_3379_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3380_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
else
{
uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3388_ = 0;
v___x_3389_ = lean_array_fget_borrowed(v_edited_3377_, v_snd_3380_);
v___x_3390_ = lean_box(v___x_3388_);
lean_inc(v___x_3389_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v___x_3389_);
lean_ctor_set(v___x_3382_, 0, v___x_3390_);
v___x_3392_ = v___x_3382_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3389_);
v___x_3392_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3393_ = lean_array_push(v_fst_3379_, v___x_3392_);
v___x_3394_ = lean_unsigned_to_nat(1u);
v___x_3395_ = lean_nat_add(v_snd_3380_, v___x_3394_);
lean_dec(v_snd_3380_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3393_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v_a_3378_ = v___x_3396_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_3400_, lean_object* v_edited_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3400_, v_edited_3401_, v_a_3402_);
lean_dec_ref(v_edited_3401_);
lean_dec(v___x_3400_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3404_, size_t v_i_3405_, lean_object* v_bs_3406_){
_start:
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_usize_dec_lt(v_i_3405_, v_sz_3404_);
if (v___x_3407_ == 0)
{
return v_bs_3406_;
}
else
{
lean_object* v_v_3408_; lean_object* v___x_3409_; lean_object* v_bs_x27_3410_; uint8_t v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; size_t v___x_3414_; size_t v___x_3415_; lean_object* v___x_3416_; 
v_v_3408_ = lean_array_uget(v_bs_3406_, v_i_3405_);
v___x_3409_ = lean_unsigned_to_nat(0u);
v_bs_x27_3410_ = lean_array_uset(v_bs_3406_, v_i_3405_, v___x_3409_);
v___x_3411_ = 0;
v___x_3412_ = lean_box(v___x_3411_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_v_3408_);
v___x_3414_ = ((size_t)1ULL);
v___x_3415_ = lean_usize_add(v_i_3405_, v___x_3414_);
v___x_3416_ = lean_array_uset(v_bs_x27_3410_, v_i_3405_, v___x_3413_);
v_i_3405_ = v___x_3415_;
v_bs_3406_ = v___x_3416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_bs_3420_){
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3421_, v_i_boxed_3422_, v_bs_3420_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3424_, size_t v_i_3425_, lean_object* v_bs_3426_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_usize_dec_lt(v_i_3425_, v_sz_3424_);
if (v___x_3427_ == 0)
{
return v_bs_3426_;
}
else
{
lean_object* v_v_3428_; lean_object* v___x_3429_; lean_object* v_bs_x27_3430_; uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; size_t v___x_3434_; size_t v___x_3435_; lean_object* v___x_3436_; 
v_v_3428_ = lean_array_uget(v_bs_3426_, v_i_3425_);
v___x_3429_ = lean_unsigned_to_nat(0u);
v_bs_x27_3430_ = lean_array_uset(v_bs_3426_, v_i_3425_, v___x_3429_);
v___x_3431_ = 1;
v___x_3432_ = lean_box(v___x_3431_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
lean_ctor_set(v___x_3433_, 1, v_v_3428_);
v___x_3434_ = ((size_t)1ULL);
v___x_3435_ = lean_usize_add(v_i_3425_, v___x_3434_);
v___x_3436_ = lean_array_uset(v_bs_x27_3430_, v_i_3425_, v___x_3433_);
v_i_3425_ = v___x_3435_;
v_bs_3426_ = v___x_3436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3438_, lean_object* v_i_3439_, lean_object* v_bs_3440_){
_start:
{
size_t v_sz_boxed_3441_; size_t v_i_boxed_3442_; lean_object* v_res_3443_; 
v_sz_boxed_3441_ = lean_unbox_usize(v_sz_3438_);
lean_dec(v_sz_3438_);
v_i_boxed_3442_ = lean_unbox_usize(v_i_3439_);
lean_dec(v_i_3439_);
v_res_3443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3441_, v_i_boxed_3442_, v_bs_3440_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3451_, lean_object* v_edited_3452_){
_start:
{
lean_object* v_i_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v_i_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = lean_array_get_size(v_original_3451_);
v___x_3455_ = lean_nat_dec_lt(v_i_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
size_t v_sz_3456_; size_t v___x_3457_; lean_object* v___x_3458_; 
lean_dec_ref(v_original_3451_);
v_sz_3456_ = lean_array_size(v_edited_3452_);
v___x_3457_ = ((size_t)0ULL);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3456_, v___x_3457_, v_edited_3452_);
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; uint8_t v___x_3460_; 
v___x_3459_ = lean_array_get_size(v_edited_3452_);
v___x_3460_ = lean_nat_dec_lt(v_i_3453_, v___x_3459_);
if (v___x_3460_ == 0)
{
size_t v_sz_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
lean_dec_ref(v_edited_3452_);
v_sz_3461_ = lean_array_size(v_original_3451_);
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3461_, v___x_3462_, v_original_3451_);
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v_ds_3466_; lean_object* v___x_3467_; size_t v_sz_3468_; size_t v___x_3469_; lean_object* v___x_3470_; lean_object* v_snd_3471_; lean_object* v_fst_3472_; lean_object* v_fst_3473_; lean_object* v_snd_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3493_; 
lean_inc_ref(v_original_3451_);
v___x_3464_ = l_Array_toSubarray___redArg(v_original_3451_, v_i_3453_, v___x_3454_);
lean_inc_ref(v_edited_3452_);
v___x_3465_ = l_Array_toSubarray___redArg(v_edited_3452_, v_i_3453_, v___x_3459_);
v_ds_3466_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3464_, v___x_3465_);
v___x_3467_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3468_ = lean_array_size(v_ds_3466_);
v___x_3469_ = ((size_t)0ULL);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3452_, v___x_3459_, v_original_3451_, v___x_3454_, v_ds_3466_, v_sz_3468_, v___x_3469_, v___x_3467_);
lean_dec_ref(v_ds_3466_);
v_snd_3471_ = lean_ctor_get(v___x_3470_, 1);
lean_inc(v_snd_3471_);
v_fst_3472_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_fst_3472_);
lean_dec_ref(v___x_3470_);
v_fst_3473_ = lean_ctor_get(v_snd_3471_, 0);
v_snd_3474_ = lean_ctor_get(v_snd_3471_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_snd_3471_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3476_ = v_snd_3471_;
v_isShared_3477_ = v_isSharedCheck_3493_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_snd_3474_);
lean_inc(v_fst_3473_);
lean_dec(v_snd_3471_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3493_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 1, v_fst_3473_);
lean_ctor_set(v___x_3476_, 0, v_fst_3472_);
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_fst_3472_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_fst_3473_);
v___x_3479_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v_fst_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3490_; 
v___x_3480_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3454_, v_original_3451_, v___x_3479_);
lean_dec_ref(v_original_3451_);
v_fst_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v___x_3480_, 1);
lean_dec(v_unused_3491_);
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3490_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_fst_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3490_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v_snd_3474_);
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3481_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_snd_3474_);
v___x_3486_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v_fst_3488_; 
v___x_3487_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3459_, v_edited_3452_, v___x_3486_);
lean_dec_ref(v_edited_3452_);
v_fst_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_fst_3488_);
lean_dec_ref(v___x_3487_);
return v_fst_3488_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
if (lean_obj_tag(v_x_3495_) == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = l_List_reverse___redArg(v_x_3496_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
else
{
lean_object* v_head_3500_; lean_object* v_tail_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3510_; 
v_head_3500_ = lean_ctor_get(v_x_3495_, 0);
v_tail_3501_ = lean_ctor_get(v_x_3495_, 1);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_x_3495_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3503_ = v_x_3495_;
v_isShared_3504_ = v_isSharedCheck_3510_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_tail_3501_);
lean_inc(v_head_3500_);
lean_dec(v_x_3495_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3510_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3500_, v___y_3494_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v_x_3496_);
lean_ctor_set(v___x_3503_, 0, v___x_3505_);
v___x_3507_ = v___x_3503_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_x_3496_);
v___x_3507_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v_x_3495_ = v_tail_3501_;
v_x_3496_ = v___x_3507_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3511_, lean_object* v_x_3512_, lean_object* v_x_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3511_, v_x_3512_, v_x_3513_);
lean_dec(v___y_3511_);
return v_res_3515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = l_Lean_MessageLog_empty;
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3641_; uint8_t v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; uint8_t v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; uint8_t v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v_dc_x3f_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3782_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3532_);
v___x_3783_ = l_Lean_Syntax_isOfKind(v_x_3532_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
lean_dec(v_x_3532_);
v___x_3784_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3784_;
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = l_Lean_Syntax_getArg(v_x_3532_, v___x_3785_);
v___x_3787_ = l_Lean_Syntax_isNone(v___x_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3788_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3786_);
v___x_3789_ = l_Lean_Syntax_matchesNull(v___x_3786_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_dec(v___x_3786_);
lean_dec(v_x_3532_);
v___x_3790_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3790_;
}
else
{
lean_object* v_dc_x3f_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v_dc_x3f_3791_ = l_Lean_Syntax_getArg(v___x_3786_, v___x_3785_);
lean_dec(v___x_3786_);
v___x_3792_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3791_);
v___x_3793_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
lean_dec(v_dc_x3f_3791_);
lean_dec(v_x_3532_);
v___x_3794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3795_, 0, v_dc_x3f_3791_);
v_dc_x3f_3763_ = v___x_3795_;
v___y_3764_ = v_a_3533_;
v___y_3765_ = v_a_3534_;
goto v___jp_3762_;
}
}
}
else
{
lean_object* v___x_3796_; 
lean_dec(v___x_3786_);
v___x_3796_ = lean_box(0);
v_dc_x3f_3763_ = v___x_3796_;
v___y_3764_ = v_a_3533_;
v___y_3765_ = v_a_3534_;
goto v___jp_3762_;
}
}
v___jp_3536_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3542_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3543_ = l_Lean_stringToMessageData(v___y_3541_);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3537_, v___x_3544_, v___y_3540_, v___y_3538_);
lean_dec(v___y_3537_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3566_; 
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3545_, 0);
lean_dec(v_unused_3567_);
v___x_3547_ = v___x_3545_;
v_isShared_3548_ = v_isSharedCheck_3566_;
goto v_resetjp_3546_;
}
else
{
lean_dec(v___x_3545_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3566_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_Elab_Command_getRef___redArg(v___y_3540_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref(v___x_3549_);
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v___y_3539_);
v___x_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_a_3550_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 10);
lean_ctor_set(v___x_3547_, 0, v___x_3553_);
v___x_3555_ = v___x_3547_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3555_, v___y_3540_, v___y_3538_);
return v___x_3556_;
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_del_object(v___x_3547_);
lean_dec_ref(v___y_3539_);
v_a_3558_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3549_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3549_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3539_);
return v___x_3545_;
}
}
v___jp_3568_:
{
if (v___y_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v_env_3579_; lean_object* v_scopes_3580_; lean_object* v_usedQuotCtxts_3581_; lean_object* v_nextMacroScope_3582_; lean_object* v_maxRecDepth_3583_; lean_object* v_ngen_3584_; lean_object* v_auxDeclNGen_3585_; lean_object* v_infoState_3586_; lean_object* v_traceState_3587_; lean_object* v_snapshotTasks_3588_; lean_object* v_newDecls_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v___y_3569_);
v___x_3578_ = lean_st_ref_take(v___y_3571_);
v_env_3579_ = lean_ctor_get(v___x_3578_, 0);
v_scopes_3580_ = lean_ctor_get(v___x_3578_, 2);
v_usedQuotCtxts_3581_ = lean_ctor_get(v___x_3578_, 3);
v_nextMacroScope_3582_ = lean_ctor_get(v___x_3578_, 4);
v_maxRecDepth_3583_ = lean_ctor_get(v___x_3578_, 5);
v_ngen_3584_ = lean_ctor_get(v___x_3578_, 6);
v_auxDeclNGen_3585_ = lean_ctor_get(v___x_3578_, 7);
v_infoState_3586_ = lean_ctor_get(v___x_3578_, 8);
v_traceState_3587_ = lean_ctor_get(v___x_3578_, 9);
v_snapshotTasks_3588_ = lean_ctor_get(v___x_3578_, 10);
v_newDecls_3589_ = lean_ctor_get(v___x_3578_, 11);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v___x_3578_, 1);
lean_dec(v_unused_3616_);
v___x_3591_ = v___x_3578_;
v_isShared_3592_ = v_isSharedCheck_3615_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_newDecls_3589_);
lean_inc(v_snapshotTasks_3588_);
lean_inc(v_traceState_3587_);
lean_inc(v_infoState_3586_);
lean_inc(v_auxDeclNGen_3585_);
lean_inc(v_ngen_3584_);
lean_inc(v_maxRecDepth_3583_);
lean_inc(v_nextMacroScope_3582_);
lean_inc(v_usedQuotCtxts_3581_);
lean_inc(v_scopes_3580_);
lean_inc(v_env_3579_);
lean_dec(v___x_3578_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3615_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 1, v___y_3576_);
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_env_3579_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___y_3576_);
lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_scopes_3580_);
lean_ctor_set(v_reuseFailAlloc_3614_, 3, v_usedQuotCtxts_3581_);
lean_ctor_set(v_reuseFailAlloc_3614_, 4, v_nextMacroScope_3582_);
lean_ctor_set(v_reuseFailAlloc_3614_, 5, v_maxRecDepth_3583_);
lean_ctor_set(v_reuseFailAlloc_3614_, 6, v_ngen_3584_);
lean_ctor_set(v_reuseFailAlloc_3614_, 7, v_auxDeclNGen_3585_);
lean_ctor_set(v_reuseFailAlloc_3614_, 8, v_infoState_3586_);
lean_ctor_set(v_reuseFailAlloc_3614_, 9, v_traceState_3587_);
lean_ctor_set(v_reuseFailAlloc_3614_, 10, v_snapshotTasks_3588_);
lean_ctor_set(v_reuseFailAlloc_3614_, 11, v_newDecls_3589_);
v___x_3594_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_scopes_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_opts_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3595_ = lean_st_ref_set(v___y_3571_, v___x_3594_);
v___x_3596_ = lean_st_ref_get(v___y_3571_);
v_scopes_3597_ = lean_ctor_get(v___x_3596_, 2);
lean_inc(v_scopes_3597_);
lean_dec(v___x_3596_);
v___x_3598_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3599_ = l_List_head_x21___redArg(v___x_3598_, v_scopes_3597_);
lean_dec(v_scopes_3597_);
v_opts_3600_ = lean_ctor_get(v___x_3599_, 1);
lean_inc_ref(v_opts_3600_);
lean_dec(v___x_3599_);
v___x_3601_ = l_guard__msgs_diff;
v___x_3602_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3600_, v___x_3601_);
lean_dec_ref(v_opts_3600_);
if (v___x_3602_ == 0)
{
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_inc_ref(v___y_3574_);
v___y_3537_ = v___y_3570_;
v___y_3538_ = v___y_3571_;
v___y_3539_ = v___y_3574_;
v___y_3540_ = v___y_3575_;
v___y_3541_ = v___y_3574_;
goto v___jp_3536_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3603_ = lean_string_utf8_byte_size(v___y_3572_);
lean_inc(v___y_3573_);
lean_inc_ref(v___y_3572_);
v___x_3604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3604_, 0, v___y_3572_);
lean_ctor_set(v___x_3604_, 1, v___y_3573_);
lean_ctor_set(v___x_3604_, 2, v___x_3603_);
v___x_3605_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3604_);
v___x_3606_ = lean_mk_empty_array_with_capacity(v___y_3573_);
lean_inc_ref(v___x_3606_);
v___x_3607_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3572_, v___x_3604_, v___x_3603_, v___x_3605_, v___x_3606_);
lean_dec_ref(v___x_3604_);
v___x_3608_ = lean_string_utf8_byte_size(v___y_3574_);
lean_inc_ref_n(v___y_3574_, 2);
v___x_3609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3609_, 0, v___y_3574_);
lean_ctor_set(v___x_3609_, 1, v___y_3573_);
lean_ctor_set(v___x_3609_, 2, v___x_3608_);
v___x_3610_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3609_);
v___x_3611_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3574_, v___x_3609_, v___x_3608_, v___x_3610_, v___x_3606_);
lean_dec_ref(v___x_3609_);
v___x_3612_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3607_, v___x_3611_);
v___x_3613_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3612_);
lean_dec_ref(v___x_3612_);
v___y_3537_ = v___y_3570_;
v___y_3538_ = v___y_3571_;
v___y_3539_ = v___y_3574_;
v___y_3540_ = v___y_3575_;
v___y_3541_ = v___x_3613_;
goto v___jp_3536_;
}
}
}
}
else
{
lean_object* v___x_3617_; lean_object* v_env_3618_; lean_object* v_scopes_3619_; lean_object* v_usedQuotCtxts_3620_; lean_object* v_nextMacroScope_3621_; lean_object* v_maxRecDepth_3622_; lean_object* v_ngen_3623_; lean_object* v_auxDeclNGen_3624_; lean_object* v_infoState_3625_; lean_object* v_traceState_3626_; lean_object* v_snapshotTasks_3627_; lean_object* v_newDecls_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v___y_3576_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3570_);
v___x_3617_ = lean_st_ref_take(v___y_3571_);
v_env_3618_ = lean_ctor_get(v___x_3617_, 0);
v_scopes_3619_ = lean_ctor_get(v___x_3617_, 2);
v_usedQuotCtxts_3620_ = lean_ctor_get(v___x_3617_, 3);
v_nextMacroScope_3621_ = lean_ctor_get(v___x_3617_, 4);
v_maxRecDepth_3622_ = lean_ctor_get(v___x_3617_, 5);
v_ngen_3623_ = lean_ctor_get(v___x_3617_, 6);
v_auxDeclNGen_3624_ = lean_ctor_get(v___x_3617_, 7);
v_infoState_3625_ = lean_ctor_get(v___x_3617_, 8);
v_traceState_3626_ = lean_ctor_get(v___x_3617_, 9);
v_snapshotTasks_3627_ = lean_ctor_get(v___x_3617_, 10);
v_newDecls_3628_ = lean_ctor_get(v___x_3617_, 11);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v___x_3617_, 1);
lean_dec(v_unused_3639_);
v___x_3630_ = v___x_3617_;
v_isShared_3631_ = v_isSharedCheck_3638_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_newDecls_3628_);
lean_inc(v_snapshotTasks_3627_);
lean_inc(v_traceState_3626_);
lean_inc(v_infoState_3625_);
lean_inc(v_auxDeclNGen_3624_);
lean_inc(v_ngen_3623_);
lean_inc(v_maxRecDepth_3622_);
lean_inc(v_nextMacroScope_3621_);
lean_inc(v_usedQuotCtxts_3620_);
lean_inc(v_scopes_3619_);
lean_inc(v_env_3618_);
lean_dec(v___x_3617_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3638_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v___y_3569_);
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_env_3618_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v___y_3569_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_scopes_3619_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_usedQuotCtxts_3620_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_nextMacroScope_3621_);
lean_ctor_set(v_reuseFailAlloc_3637_, 5, v_maxRecDepth_3622_);
lean_ctor_set(v_reuseFailAlloc_3637_, 6, v_ngen_3623_);
lean_ctor_set(v_reuseFailAlloc_3637_, 7, v_auxDeclNGen_3624_);
lean_ctor_set(v_reuseFailAlloc_3637_, 8, v_infoState_3625_);
lean_ctor_set(v_reuseFailAlloc_3637_, 9, v_traceState_3626_);
lean_ctor_set(v_reuseFailAlloc_3637_, 10, v_snapshotTasks_3627_);
lean_ctor_set(v_reuseFailAlloc_3637_, 11, v_newDecls_3628_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = lean_st_ref_set(v___y_3571_, v___x_3633_);
v___x_3635_ = lean_box(0);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
}
}
}
v___jp_3640_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_a_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v_str_3663_; lean_object* v_startInclusive_3664_; lean_object* v_endExclusive_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3680_; 
v___x_3653_ = l_Lean_MessageLog_toList(v___y_3645_);
lean_dec(v___y_3645_);
v___x_3654_ = lean_box(0);
v___x_3655_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3652_, v___x_3653_, v___x_3654_);
lean_dec(v___y_3652_);
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref(v___x_3655_);
v___x_3657_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3649_, v_a_3656_);
v___x_3658_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3659_ = l_String_intercalate(v___x_3658_, v___x_3657_);
v___x_3660_ = lean_string_utf8_byte_size(v___x_3659_);
lean_inc(v___y_3648_);
v___x_3661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___y_3648_);
lean_ctor_set(v___x_3661_, 2, v___x_3660_);
v___x_3662_ = l_String_Slice_trimAscii(v___x_3661_);
v_str_3663_ = lean_ctor_get(v___x_3662_, 0);
v_startInclusive_3664_ = lean_ctor_get(v___x_3662_, 1);
v_endExclusive_3665_ = lean_ctor_get(v___x_3662_, 2);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3667_ = v___x_3662_;
v_isShared_3668_ = v_isSharedCheck_3680_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_endExclusive_3665_);
lean_inc(v_startInclusive_3664_);
lean_inc(v_str_3663_);
lean_dec(v___x_3662_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3680_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_string_utf8_extract(v_str_3663_, v_startInclusive_3664_, v_endExclusive_3665_);
lean_dec(v_endExclusive_3665_);
lean_dec(v_startInclusive_3664_);
lean_dec_ref(v_str_3663_);
if (v___y_3642_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
lean_del_object(v___x_3667_);
lean_inc_ref(v___y_3647_);
v___x_3670_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3646_, v___y_3647_);
lean_inc_ref(v___x_3669_);
v___x_3671_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3646_, v___x_3669_);
v___x_3672_ = lean_string_dec_eq(v___x_3670_, v___x_3671_);
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3670_);
v___y_3569_ = v___y_3641_;
v___y_3570_ = v___y_3643_;
v___y_3571_ = v___y_3644_;
v___y_3572_ = v___y_3647_;
v___y_3573_ = v___y_3648_;
v___y_3574_ = v___x_3669_;
v___y_3575_ = v___y_3651_;
v___y_3576_ = v___y_3650_;
v___y_3577_ = v___x_3672_;
goto v___jp_3568_;
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
lean_inc_ref(v___x_3669_);
v___x_3673_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3646_, v___x_3669_);
lean_inc_ref(v___y_3647_);
v___x_3674_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3646_, v___y_3647_);
v___x_3675_ = lean_string_utf8_byte_size(v___x_3673_);
lean_inc(v___y_3648_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 2, v___x_3675_);
lean_ctor_set(v___x_3667_, 1, v___y_3648_);
lean_ctor_set(v___x_3667_, 0, v___x_3673_);
v___x_3677_ = v___x_3667_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___y_3648_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
uint8_t v___x_3678_; 
v___x_3678_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3674_, v___x_3677_);
lean_dec_ref(v___x_3677_);
v___y_3569_ = v___y_3641_;
v___y_3570_ = v___y_3643_;
v___y_3571_ = v___y_3644_;
v___y_3572_ = v___y_3647_;
v___y_3573_ = v___y_3648_;
v___y_3574_ = v___x_3669_;
v___y_3575_ = v___y_3651_;
v___y_3576_ = v___y_3650_;
v___y_3577_ = v___x_3678_;
goto v___jp_3568_;
}
}
}
}
v___jp_3681_:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3685_, v___y_3686_, v___y_3684_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v_filterFn_3690_; uint8_t v_whitespace_3691_; uint8_t v_ordering_3692_; uint8_t v_reportPositions_3693_; uint8_t v_substring_3694_; lean_object* v___x_3695_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___x_3688_);
v_filterFn_3690_ = lean_ctor_get(v_a_3689_, 0);
lean_inc_ref(v_filterFn_3690_);
v_whitespace_3691_ = lean_ctor_get_uint8(v_a_3689_, sizeof(void*)*1);
v_ordering_3692_ = lean_ctor_get_uint8(v_a_3689_, sizeof(void*)*1 + 1);
v_reportPositions_3693_ = lean_ctor_get_uint8(v_a_3689_, sizeof(void*)*1 + 2);
v_substring_3694_ = lean_ctor_get_uint8(v_a_3689_, sizeof(void*)*1 + 3);
lean_dec(v_a_3689_);
v___x_3695_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3683_, v___y_3686_, v___y_3684_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v_a_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v_str_3705_; lean_object* v_startInclusive_3706_; lean_object* v_endExclusive_3707_; lean_object* v_fst_3708_; lean_object* v_snd_3709_; lean_object* v_fileMap_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = l_Lean_MessageLog_toList(v_a_3696_);
v___x_3698_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3699_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3690_, v___x_3697_, v___x_3698_);
lean_dec(v___x_3697_);
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref(v___x_3699_);
v___x_3701_ = lean_unsigned_to_nat(0u);
v___x_3702_ = lean_string_utf8_byte_size(v___y_3687_);
v___x_3703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3703_, 0, v___y_3687_);
lean_ctor_set(v___x_3703_, 1, v___x_3701_);
lean_ctor_set(v___x_3703_, 2, v___x_3702_);
v___x_3704_ = l_String_Slice_trimAscii(v___x_3703_);
v_str_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc_ref(v_str_3705_);
v_startInclusive_3706_ = lean_ctor_get(v___x_3704_, 1);
lean_inc(v_startInclusive_3706_);
v_endExclusive_3707_ = lean_ctor_get(v___x_3704_, 2);
lean_inc(v_endExclusive_3707_);
lean_dec_ref(v___x_3704_);
v_fst_3708_ = lean_ctor_get(v_a_3700_, 0);
lean_inc(v_fst_3708_);
v_snd_3709_ = lean_ctor_get(v_a_3700_, 1);
lean_inc(v_snd_3709_);
lean_dec(v_a_3700_);
v_fileMap_3710_ = lean_ctor_get(v___y_3686_, 1);
v___x_3711_ = lean_string_utf8_extract(v_str_3705_, v_startInclusive_3706_, v_endExclusive_3707_);
lean_dec(v_endExclusive_3707_);
lean_dec(v_startInclusive_3706_);
lean_dec_ref(v_str_3705_);
v___x_3712_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3711_);
if (v_reportPositions_3693_ == 0)
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_box(0);
v___y_3641_ = v_snd_3709_;
v___y_3642_ = v_substring_3694_;
v___y_3643_ = v___y_3682_;
v___y_3644_ = v___y_3684_;
v___y_3645_ = v_fst_3708_;
v___y_3646_ = v_whitespace_3691_;
v___y_3647_ = v___x_3712_;
v___y_3648_ = v___x_3701_;
v___y_3649_ = v_ordering_3692_;
v___y_3650_ = v_a_3696_;
v___y_3651_ = v___y_3686_;
v___y_3652_ = v___x_3713_;
goto v___jp_3640_;
}
else
{
uint8_t v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = 0;
v___x_3715_ = l_Lean_Syntax_getPos_x3f(v___y_3682_, v___x_3714_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_box(0);
v___y_3641_ = v_snd_3709_;
v___y_3642_ = v_substring_3694_;
v___y_3643_ = v___y_3682_;
v___y_3644_ = v___y_3684_;
v___y_3645_ = v_fst_3708_;
v___y_3646_ = v_whitespace_3691_;
v___y_3647_ = v___x_3712_;
v___y_3648_ = v___x_3701_;
v___y_3649_ = v_ordering_3692_;
v___y_3650_ = v_a_3696_;
v___y_3651_ = v___y_3686_;
v___y_3652_ = v___x_3716_;
goto v___jp_3640_;
}
else
{
lean_object* v_val_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3726_; 
v_val_3717_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3719_ = v___x_3715_;
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_val_3717_);
lean_dec(v___x_3715_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v_line_3722_; lean_object* v___x_3724_; 
lean_inc_ref(v_fileMap_3710_);
v___x_3721_ = l_Lean_FileMap_toPosition(v_fileMap_3710_, v_val_3717_);
lean_dec(v_val_3717_);
v_line_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_line_3722_);
lean_dec_ref(v___x_3721_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v_line_3722_);
v___x_3724_ = v___x_3719_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_line_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
v___y_3641_ = v_snd_3709_;
v___y_3642_ = v_substring_3694_;
v___y_3643_ = v___y_3682_;
v___y_3644_ = v___y_3684_;
v___y_3645_ = v_fst_3708_;
v___y_3646_ = v_whitespace_3691_;
v___y_3647_ = v___x_3712_;
v___y_3648_ = v___x_3701_;
v___y_3649_ = v_ordering_3692_;
v___y_3650_ = v_a_3696_;
v___y_3651_ = v___y_3686_;
v___y_3652_ = v___x_3724_;
goto v___jp_3640_;
}
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec_ref(v_filterFn_3690_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3682_);
v_a_3727_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3695_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3695_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3683_);
lean_dec(v___y_3682_);
v_a_3735_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3688_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3688_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
v___jp_3743_:
{
if (lean_obj_tag(v___y_3747_) == 0)
{
lean_object* v___x_3750_; 
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3682_ = v___y_3744_;
v___y_3683_ = v___y_3745_;
v___y_3684_ = v___y_3746_;
v___y_3685_ = v___y_3749_;
v___y_3686_ = v___y_3748_;
v___y_3687_ = v___x_3750_;
goto v___jp_3681_;
}
else
{
lean_object* v_val_3751_; lean_object* v___x_3752_; 
v_val_3751_ = lean_ctor_get(v___y_3747_, 0);
lean_inc(v_val_3751_);
lean_dec_ref(v___y_3747_);
v___x_3752_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3751_, v___y_3748_, v___y_3746_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref(v___x_3752_);
v___y_3682_ = v___y_3744_;
v___y_3683_ = v___y_3745_;
v___y_3684_ = v___y_3746_;
v___y_3685_ = v___y_3749_;
v___y_3686_ = v___y_3748_;
v___y_3687_ = v_a_3753_;
goto v___jp_3681_;
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v___y_3749_);
lean_dec(v___y_3745_);
lean_dec(v___y_3744_);
v_a_3754_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3752_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3752_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
v___jp_3762_:
{
lean_object* v___x_3766_; lean_object* v_tk_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3766_ = lean_unsigned_to_nat(1u);
v_tk_3767_ = l_Lean_Syntax_getArg(v_x_3532_, v___x_3766_);
v___x_3768_ = lean_unsigned_to_nat(2u);
v___x_3769_ = l_Lean_Syntax_getArg(v_x_3532_, v___x_3768_);
v___x_3770_ = lean_unsigned_to_nat(4u);
v___x_3771_ = l_Lean_Syntax_getArg(v_x_3532_, v___x_3770_);
lean_dec(v_x_3532_);
v___x_3772_ = l_Lean_Syntax_getOptional_x3f(v___x_3769_);
lean_dec(v___x_3769_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_box(0);
v___y_3744_ = v_tk_3767_;
v___y_3745_ = v___x_3771_;
v___y_3746_ = v___y_3765_;
v___y_3747_ = v_dc_x3f_3763_;
v___y_3748_ = v___y_3764_;
v___y_3749_ = v___x_3773_;
goto v___jp_3743_;
}
else
{
lean_object* v_val_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
v_val_3774_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3772_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_val_3774_);
lean_dec(v___x_3772_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_val_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
v___y_3744_ = v_tk_3767_;
v___y_3745_ = v___x_3771_;
v___y_3746_ = v___y_3765_;
v___y_3747_ = v_dc_x3f_3763_;
v___y_3748_ = v___y_3764_;
v___y_3749_ = v___x_3779_;
goto v___jp_3743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3802_, lean_object* v_as_3803_, lean_object* v_as_x27_3804_, lean_object* v_b_3805_, lean_object* v_a_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3802_, v_as_x27_3804_, v_b_3805_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3811_, lean_object* v_as_3812_, lean_object* v_as_x27_3813_, lean_object* v_b_3814_, lean_object* v_a_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3811_, v_as_3812_, v_as_x27_3813_, v_b_3814_, v_a_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v_as_x27_3813_);
lean_dec(v_as_3812_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3820_, lean_object* v_x_3821_, lean_object* v_x_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3820_, v_x_3821_, v_x_3822_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3827_, lean_object* v_x_3828_, lean_object* v_x_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3827_, v_x_3828_, v_x_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3827_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3834_, v___y_3836_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v_inst_3847_, lean_object* v_R_3848_, lean_object* v_a_3849_, lean_object* v_b_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3844_, v___x_3845_, v___x_3846_, v_a_3849_, v_b_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3852_, lean_object* v___x_3853_, lean_object* v___x_3854_, lean_object* v_inst_3855_, lean_object* v_R_3856_, lean_object* v_a_3857_, lean_object* v_b_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3852_, v___x_3853_, v___x_3854_, v_inst_3855_, v_R_3856_, v_a_3857_, v_b_3858_);
lean_dec_ref(v___x_3853_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3860_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3870_, lean_object* v___x_3871_, lean_object* v___x_3872_, lean_object* v_inst_3873_, lean_object* v_R_3874_, lean_object* v_a_3875_, lean_object* v_b_3876_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3870_, v___x_3871_, v___x_3872_, v_a_3875_, v_b_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3878_, lean_object* v___x_3879_, lean_object* v___x_3880_, lean_object* v_inst_3881_, lean_object* v_R_3882_, lean_object* v_a_3883_, lean_object* v_b_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3878_, v___x_3879_, v___x_3880_, v_inst_3881_, v_R_3882_, v_a_3883_, v_b_3884_);
lean_dec_ref(v___x_3879_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_3886_, lean_object* v___x_3887_, lean_object* v_a_3888_, lean_object* v_inst_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3886_, v___x_3887_, v_a_3888_, v_a_3890_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_3892_, lean_object* v___x_3893_, lean_object* v_a_3894_, lean_object* v_inst_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_3892_, v___x_3893_, v_a_3894_, v_inst_3895_, v_a_3896_);
lean_dec_ref(v_a_3894_);
lean_dec(v___x_3893_);
lean_dec_ref(v_original_3892_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_3898_, lean_object* v___x_3899_, lean_object* v_a_3900_, lean_object* v_inst_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3898_, v___x_3899_, v_a_3900_, v_a_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_3904_, lean_object* v___x_3905_, lean_object* v_a_3906_, lean_object* v_inst_3907_, lean_object* v_a_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_3904_, v___x_3905_, v_a_3906_, v_inst_3907_, v_a_3908_);
lean_dec_ref(v_a_3906_);
lean_dec(v___x_3905_);
lean_dec_ref(v_edited_3904_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3910_, lean_object* v_original_3911_, lean_object* v_inst_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3910_, v_original_3911_, v_a_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3915_, lean_object* v_original_3916_, lean_object* v_inst_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3915_, v_original_3916_, v_inst_3917_, v_a_3918_);
lean_dec_ref(v_original_3916_);
lean_dec(v___x_3915_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3920_, lean_object* v_edited_3921_, lean_object* v_inst_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3920_, v_edited_3921_, v_a_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3925_, lean_object* v_edited_3926_, lean_object* v_inst_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l___private_Init_While_0__whileM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3925_, v_edited_3926_, v_inst_3927_, v_a_3928_);
lean_dec_ref(v_edited_3926_);
lean_dec(v___x_3925_);
return v_res_3929_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3930_, lean_object* v_inst_3931_, lean_object* v_R_3932_, lean_object* v_a_3933_, uint8_t v_b_3934_, lean_object* v_c_3935_){
_start:
{
uint8_t v___x_3936_; 
v___x_3936_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3930_, v_a_3933_, v_b_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3937_, lean_object* v_inst_3938_, lean_object* v_R_3939_, lean_object* v_a_3940_, lean_object* v_b_3941_, lean_object* v_c_3942_){
_start:
{
uint8_t v_b_boxed_3943_; uint8_t v_res_3944_; lean_object* v_r_3945_; 
v_b_boxed_3943_ = lean_unbox(v_b_3941_);
v_res_3944_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3937_, v_inst_3938_, v_R_3939_, v_a_3940_, v_b_boxed_3943_, v_c_3942_);
lean_dec_ref(v_s_3937_);
v_r_3945_ = lean_box(v_res_3944_);
return v_r_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3946_, lean_object* v_ref_3947_, lean_object* v_msg_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3947_, v_msg_3948_, v___y_3949_, v___y_3950_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3953_, lean_object* v_ref_3954_, lean_object* v_msg_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3953_, v_ref_3954_, v_msg_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v_ref_3954_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3960_, lean_object* v_as_x27_3961_, lean_object* v_b_3962_, lean_object* v_a_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3961_, v_b_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3965_, lean_object* v_as_x27_3966_, lean_object* v_b_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3965_, v_as_x27_3966_, v_b_3967_, v_a_3968_);
lean_dec(v_as_x27_3966_);
lean_dec(v_as_3965_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3970_, lean_object* v_rsize_3971_, lean_object* v_histogram_3972_, lean_object* v_index_3973_, lean_object* v_val_3974_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3972_, v_index_3973_, v_val_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3976_, lean_object* v_rsize_3977_, lean_object* v_histogram_3978_, lean_object* v_index_3979_, lean_object* v_val_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3976_, v_rsize_3977_, v_histogram_3978_, v_index_3979_, v_val_3980_);
lean_dec(v_rsize_3977_);
lean_dec(v_lsize_3976_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3982_, lean_object* v___x_3983_, lean_object* v_fst_3984_, lean_object* v___x_3985_, lean_object* v_inst_3986_, lean_object* v_R_3987_, lean_object* v_a_3988_, lean_object* v_b_3989_, lean_object* v_c_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3982_, v___x_3983_, v_fst_3984_, v___x_3985_, v_a_3988_, v_b_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3992_, lean_object* v___x_3993_, lean_object* v_fst_3994_, lean_object* v___x_3995_, lean_object* v_inst_3996_, lean_object* v_R_3997_, lean_object* v_a_3998_, lean_object* v_b_3999_, lean_object* v_c_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3992_, v___x_3993_, v_fst_3994_, v___x_3995_, v_inst_3996_, v_R_3997_, v_a_3998_, v_b_3999_, v_c_4000_);
lean_dec(v___x_3995_);
lean_dec_ref(v_fst_3994_);
lean_dec(v___x_3993_);
lean_dec(v_upperBound_3992_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_4002_, lean_object* v_rsize_4003_, lean_object* v_histogram_4004_, lean_object* v_index_4005_, lean_object* v_val_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_4004_, v_index_4005_, v_val_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_4008_, lean_object* v_rsize_4009_, lean_object* v_histogram_4010_, lean_object* v_index_4011_, lean_object* v_val_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_4008_, v_rsize_4009_, v_histogram_4010_, v_index_4011_, v_val_4012_);
lean_dec(v_rsize_4009_);
lean_dec(v_lsize_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_4014_, lean_object* v_fst_4015_, lean_object* v___x_4016_, lean_object* v_fst_4017_, lean_object* v_inst_4018_, lean_object* v_R_4019_, lean_object* v_a_4020_, lean_object* v_b_4021_, lean_object* v_c_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_4014_, v_fst_4015_, v___x_4016_, v_fst_4017_, v_a_4020_, v_b_4021_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_4024_, lean_object* v_fst_4025_, lean_object* v___x_4026_, lean_object* v_fst_4027_, lean_object* v_inst_4028_, lean_object* v_R_4029_, lean_object* v_a_4030_, lean_object* v_b_4031_, lean_object* v_c_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_4024_, v_fst_4025_, v___x_4026_, v_fst_4027_, v_inst_4028_, v_R_4029_, v_a_4030_, v_b_4031_, v_c_4032_);
lean_dec_ref(v_fst_4027_);
lean_dec(v___x_4026_);
lean_dec_ref(v_fst_4025_);
lean_dec(v_upperBound_4024_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4034_, lean_object* v_msg_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4035_, v___y_4036_, v___y_4037_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4040_, lean_object* v_msg_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4040_, v_msg_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_4046_, lean_object* v_m_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_4047_, v_a_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_4050_, lean_object* v_m_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_4050_, v_m_4051_, v_a_4052_);
lean_dec_ref(v_a_4052_);
lean_dec_ref(v_m_4051_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_4054_, lean_object* v_m_4055_, lean_object* v_a_4056_, lean_object* v_b_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_4055_, v_a_4056_, v_b_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4059_, lean_object* v_macroStack_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4059_, v_macroStack_4060_, v___y_4062_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4065_, lean_object* v_macroStack_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4065_, v_macroStack_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4071_, lean_object* v_R_4072_, lean_object* v_a_4073_, lean_object* v_b_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4073_, v_b_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4076_, lean_object* v_a_4077_, lean_object* v_x_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4077_, v_x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4080_, lean_object* v_a_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4080_, v_a_4081_, v_x_4082_);
lean_dec(v_x_4082_);
lean_dec_ref(v_a_4081_);
return v_res_4083_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4084_, lean_object* v_a_4085_, lean_object* v_x_4086_){
_start:
{
uint8_t v___x_4087_; 
v___x_4087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4085_, v_x_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4088_, lean_object* v_a_4089_, lean_object* v_x_4090_){
_start:
{
uint8_t v_res_4091_; lean_object* v_r_4092_; 
v_res_4091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4088_, v_a_4089_, v_x_4090_);
lean_dec(v_x_4090_);
lean_dec_ref(v_a_4089_);
v_r_4092_ = lean_box(v_res_4091_);
return v_r_4092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4093_, lean_object* v_data_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4096_, lean_object* v_a_4097_, lean_object* v_b_4098_, lean_object* v_x_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4097_, v_b_4098_, v_x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4101_, lean_object* v_i_4102_, lean_object* v_source_4103_, lean_object* v_target_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4102_, v_source_4103_, v_target_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4106_, lean_object* v_x_4107_, lean_object* v_x_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4107_, v_x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4118_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4120_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4121_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4122_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4118_, v___x_4119_, v___x_4120_, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4151_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4152_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4153_ = l_Lean_addBuiltinDeclarationRanges(v___x_4151_, v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4156_){
_start:
{
lean_object* v_doc_4158_; lean_object* v___x_4159_; 
v_doc_4158_ = lean_ctor_get(v___y_4156_, 1);
lean_inc_ref(v_doc_4158_);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v_doc_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4160_);
lean_dec_ref(v___y_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4163_, lean_object* v_a_4164_, uint8_t v_b_4165_){
_start:
{
lean_object* v_str_4166_; lean_object* v_startInclusive_4167_; lean_object* v_endExclusive_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v_str_4166_ = lean_ctor_get(v_s_4163_, 0);
v_startInclusive_4167_ = lean_ctor_get(v_s_4163_, 1);
v_endExclusive_4168_ = lean_ctor_get(v_s_4163_, 2);
v___x_4169_ = lean_nat_sub(v_endExclusive_4168_, v_startInclusive_4167_);
v___x_4170_ = lean_nat_dec_eq(v_a_4164_, v___x_4169_);
lean_dec(v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; uint32_t v___x_4172_; uint32_t v___x_4173_; uint8_t v___x_4174_; 
v___x_4171_ = lean_nat_add(v_startInclusive_4167_, v_a_4164_);
lean_dec(v_a_4164_);
v___x_4172_ = lean_string_utf8_get_fast(v_str_4166_, v___x_4171_);
v___x_4173_ = 10;
v___x_4174_ = lean_uint32_dec_eq(v___x_4172_, v___x_4173_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_string_utf8_next_fast(v_str_4166_, v___x_4171_);
lean_dec(v___x_4171_);
v___x_4176_ = lean_nat_sub(v___x_4175_, v_startInclusive_4167_);
v_a_4164_ = v___x_4176_;
v_b_4165_ = v___x_4174_;
goto _start;
}
else
{
lean_dec(v___x_4171_);
return v___x_4174_;
}
}
else
{
lean_dec(v_a_4164_);
return v_b_4165_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4178_, lean_object* v_a_4179_, lean_object* v_b_4180_){
_start:
{
uint8_t v_b_boxed_4181_; uint8_t v_res_4182_; lean_object* v_r_4183_; 
v_b_boxed_4181_ = lean_unbox(v_b_4180_);
v_res_4182_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4178_, v_a_4179_, v_b_boxed_4181_);
lean_dec_ref(v_s_4178_);
v_r_4183_ = lean_box(v_res_4182_);
return v_r_4183_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4184_){
_start:
{
lean_object* v_searcher_4185_; uint8_t v___x_4186_; uint8_t v___x_4187_; 
v_searcher_4185_ = lean_unsigned_to_nat(0u);
v___x_4186_ = 0;
v___x_4187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4184_, v_searcher_4185_, v___x_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4188_){
_start:
{
uint8_t v_res_4189_; lean_object* v_r_4190_; 
v_res_4189_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4188_);
lean_dec_ref(v_s_4188_);
v_r_4190_ = lean_box(v_res_4189_);
return v_r_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4202_, lean_object* v_fst_4203_, uint8_t v___x_4204_, lean_object* v_a_4205_, lean_object* v___x_4206_, lean_object* v___x_4207_, lean_object* v___x_4208_, lean_object* v___x_4209_, lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v_snd_4214_, lean_object* v___x_4215_){
_start:
{
if (lean_obj_tag(v___x_4202_) == 1)
{
lean_object* v_val_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4280_; 
v_val_4217_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4219_ = v___x_4202_;
v_isShared_4220_ = v_isSharedCheck_4280_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_val_4217_);
lean_dec(v___x_4202_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4280_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4221_ = lean_unsigned_to_nat(0u);
v___x_4222_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4223_ = l_Lean_Syntax_setArg(v_fst_4203_, v___x_4221_, v___x_4222_);
v___x_4224_ = l_Lean_Syntax_getPos_x3f(v___x_4223_, v___x_4204_);
lean_dec(v___x_4223_);
if (lean_obj_tag(v___x_4224_) == 1)
{
lean_object* v_val_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v___x_4215_);
v_val_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4276_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_val_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4276_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___y_4230_; lean_object* v___x_4256_; uint8_t v___y_4263_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v___x_4256_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4214_);
v___x_4268_ = lean_string_utf8_byte_size(v___x_4256_);
v___x_4269_ = lean_nat_dec_eq(v___x_4268_, v___x_4221_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v___x_4270_ = lean_string_length(v___x_4256_);
v___x_4271_ = lean_unsigned_to_nat(93u);
v___x_4272_ = lean_nat_dec_le(v___x_4270_, v___x_4271_);
if (v___x_4272_ == 0)
{
v___y_4263_ = v___x_4272_;
goto v___jp_4262_;
}
else
{
lean_object* v___x_4273_; uint8_t v___x_4274_; 
lean_inc_ref(v___x_4256_);
v___x_4273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4256_);
lean_ctor_set(v___x_4273_, 1, v___x_4221_);
lean_ctor_set(v___x_4273_, 2, v___x_4268_);
v___x_4274_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4273_);
lean_dec_ref(v___x_4273_);
if (v___x_4274_ == 0)
{
v___y_4263_ = v___x_4272_;
goto v___jp_4262_;
}
else
{
goto v___jp_4257_;
}
}
}
else
{
lean_object* v___x_4275_; 
lean_dec_ref(v___x_4256_);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4230_ = v___x_4275_;
goto v___jp_4229_;
}
v___jp_4229_:
{
lean_object* v_toEditableDocumentCore_4231_; lean_object* v_meta_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4252_; 
v_toEditableDocumentCore_4231_ = lean_ctor_get(v_a_4205_, 0);
lean_inc_ref(v_toEditableDocumentCore_4231_);
v_meta_4232_ = lean_ctor_get(v_toEditableDocumentCore_4231_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v_toEditableDocumentCore_4231_);
if (v_isSharedCheck_4252_ == 0)
{
lean_object* v_unused_4253_; lean_object* v_unused_4254_; lean_object* v_unused_4255_; 
v_unused_4253_ = lean_ctor_get(v_toEditableDocumentCore_4231_, 3);
lean_dec(v_unused_4253_);
v_unused_4254_ = lean_ctor_get(v_toEditableDocumentCore_4231_, 2);
lean_dec(v_unused_4254_);
v_unused_4255_ = lean_ctor_get(v_toEditableDocumentCore_4231_, 1);
lean_dec(v_unused_4255_);
v___x_4234_ = v_toEditableDocumentCore_4231_;
v_isShared_4235_ = v_isSharedCheck_4252_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_meta_4232_);
lean_dec(v_toEditableDocumentCore_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4252_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v_text_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4242_; 
v_text_4236_ = lean_ctor_get(v_meta_4232_, 3);
lean_inc_ref(v_text_4236_);
lean_dec_ref(v_meta_4232_);
v___x_4237_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4205_);
v___x_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4238_, 0, v_val_4217_);
lean_ctor_set(v___x_4238_, 1, v_val_4225_);
v___x_4239_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4236_, v___x_4238_);
v___x_4240_ = lean_box(0);
lean_inc(v___x_4206_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 3, v___x_4206_);
lean_ctor_set(v___x_4234_, 2, v___x_4240_);
lean_ctor_set(v___x_4234_, 1, v___y_4230_);
lean_ctor_set(v___x_4234_, 0, v___x_4239_);
v___x_4242_ = v___x_4234_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v___y_4230_);
lean_ctor_set(v_reuseFailAlloc_4251_, 2, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4251_, 3, v___x_4206_);
v___x_4242_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4243_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4237_, v___x_4242_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4243_);
v___x_4245_ = v___x_4227_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4246_; lean_object* v___x_4248_; 
lean_inc(v___x_4206_);
v___x_4246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4206_);
lean_ctor_set(v___x_4246_, 1, v___x_4206_);
lean_ctor_set(v___x_4246_, 2, v___x_4207_);
lean_ctor_set(v___x_4246_, 3, v___x_4208_);
lean_ctor_set(v___x_4246_, 4, v___x_4209_);
lean_ctor_set(v___x_4246_, 5, v___x_4210_);
lean_ctor_set(v___x_4246_, 6, v___x_4211_);
lean_ctor_set(v___x_4246_, 7, v___x_4245_);
lean_ctor_set(v___x_4246_, 8, v___x_4212_);
lean_ctor_set(v___x_4246_, 9, v___x_4213_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set_tag(v___x_4219_, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4246_);
v___x_4248_ = v___x_4219_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
v___jp_4257_:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4259_ = lean_string_append(v___x_4258_, v___x_4256_);
lean_dec_ref(v___x_4256_);
v___x_4260_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4261_ = lean_string_append(v___x_4259_, v___x_4260_);
v___y_4230_ = v___x_4261_;
goto v___jp_4229_;
}
v___jp_4262_:
{
if (v___y_4263_ == 0)
{
goto v___jp_4257_;
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4264_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4265_ = lean_string_append(v___x_4264_, v___x_4256_);
lean_dec_ref(v___x_4256_);
v___x_4266_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4267_ = lean_string_append(v___x_4265_, v___x_4266_);
v___y_4230_ = v___x_4267_;
goto v___jp_4229_;
}
}
}
}
else
{
lean_object* v___x_4278_; 
lean_dec(v___x_4224_);
lean_dec(v_val_4217_);
lean_dec_ref(v_snd_4214_);
lean_dec(v___x_4213_);
lean_dec(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec(v___x_4209_);
lean_dec(v___x_4208_);
lean_dec_ref(v___x_4207_);
lean_dec(v___x_4206_);
lean_dec_ref(v_a_4205_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set_tag(v___x_4219_, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4215_);
v___x_4278_ = v___x_4219_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4215_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
lean_object* v___x_4281_; 
lean_dec_ref(v_snd_4214_);
lean_dec(v___x_4213_);
lean_dec(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec(v___x_4209_);
lean_dec(v___x_4208_);
lean_dec_ref(v___x_4207_);
lean_dec(v___x_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_fst_4203_);
lean_dec(v___x_4202_);
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4215_);
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4282_, lean_object* v_fst_4283_, lean_object* v___x_4284_, lean_object* v_a_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v___x_4290_, lean_object* v___x_4291_, lean_object* v___x_4292_, lean_object* v___x_4293_, lean_object* v_snd_4294_, lean_object* v___x_4295_, lean_object* v___y_4296_){
_start:
{
uint8_t v___x_4549__boxed_4297_; lean_object* v_res_4298_; 
v___x_4549__boxed_4297_ = lean_unbox(v___x_4284_);
v_res_4298_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4282_, v_fst_4283_, v___x_4549__boxed_4297_, v_a_4285_, v___x_4286_, v___x_4287_, v___x_4288_, v___x_4289_, v___x_4290_, v___x_4291_, v___x_4292_, v___x_4293_, v_snd_4294_, v___x_4295_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4302_, size_t v_sz_4303_, size_t v_i_4304_, lean_object* v_b_4305_){
_start:
{
lean_object* v_a_4307_; uint8_t v___x_4311_; 
v___x_4311_ = lean_usize_dec_lt(v_i_4304_, v_sz_4303_);
if (v___x_4311_ == 0)
{
lean_inc_ref(v_b_4305_);
return v_b_4305_;
}
else
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v_a_4314_; 
v___x_4312_ = lean_box(0);
v___x_4313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4314_ = lean_array_uget(v_as_4302_, v_i_4304_);
if (lean_obj_tag(v_a_4314_) == 1)
{
lean_object* v_i_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4349_; 
v_i_4315_ = lean_ctor_get(v_a_4314_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_a_4314_);
if (v_isSharedCheck_4349_ == 0)
{
lean_object* v_unused_4350_; 
v_unused_4350_ = lean_ctor_get(v_a_4314_, 1);
lean_dec(v_unused_4350_);
v___x_4317_ = v_a_4314_;
v_isShared_4318_ = v_isSharedCheck_4349_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_i_4315_);
lean_dec(v_a_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4349_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
if (lean_obj_tag(v_i_4315_) == 10)
{
lean_object* v_i_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4348_; 
v_i_4319_ = lean_ctor_get(v_i_4315_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_i_4315_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4321_ = v_i_4315_;
v_isShared_4322_ = v_isSharedCheck_4348_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_i_4319_);
lean_dec(v_i_4315_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4348_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v_stx_4323_; lean_object* v_value_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4347_; 
v_stx_4323_ = lean_ctor_get(v_i_4319_, 0);
v_value_4324_ = lean_ctor_get(v_i_4319_, 1);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_i_4319_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4326_ = v_i_4319_;
v_isShared_4327_ = v_isSharedCheck_4347_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_value_4324_);
lean_inc(v_stx_4323_);
lean_dec(v_i_4319_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4347_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4328_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4329_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4324_, v___x_4328_);
lean_dec(v_value_4324_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_del_object(v___x_4326_);
lean_dec(v_stx_4323_);
lean_del_object(v___x_4321_);
lean_del_object(v___x_4317_);
v_a_4307_ = v___x_4313_;
goto v___jp_4306_;
}
else
{
lean_object* v_val_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4346_; 
v_val_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4346_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_val_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4346_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 1, v_val_4330_);
v___x_4335_ = v___x_4326_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_stx_4323_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_val_4330_);
v___x_4335_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4335_);
v___x_4337_ = v___x_4332_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4339_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 1);
lean_ctor_set(v___x_4321_, 0, v___x_4337_);
v___x_4339_ = v___x_4321_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4341_; 
if (v_isShared_4318_ == 0)
{
lean_ctor_set_tag(v___x_4317_, 0);
lean_ctor_set(v___x_4317_, 1, v___x_4312_);
lean_ctor_set(v___x_4317_, 0, v___x_4339_);
v___x_4341_ = v___x_4317_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v___x_4312_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
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
lean_del_object(v___x_4317_);
lean_dec_ref(v_i_4315_);
v_a_4307_ = v___x_4313_;
goto v___jp_4306_;
}
}
}
else
{
lean_dec(v_a_4314_);
v_a_4307_ = v___x_4313_;
goto v___jp_4306_;
}
}
v___jp_4306_:
{
size_t v___x_4308_; size_t v___x_4309_; 
v___x_4308_ = ((size_t)1ULL);
v___x_4309_ = lean_usize_add(v_i_4304_, v___x_4308_);
v_i_4304_ = v___x_4309_;
v_b_4305_ = v_a_4307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4351_, lean_object* v_sz_4352_, lean_object* v_i_4353_, lean_object* v_b_4354_){
_start:
{
size_t v_sz_boxed_4355_; size_t v_i_boxed_4356_; lean_object* v_res_4357_; 
v_sz_boxed_4355_ = lean_unbox_usize(v_sz_4352_);
lean_dec(v_sz_4352_);
v_i_boxed_4356_ = lean_unbox_usize(v_i_4353_);
lean_dec(v_i_4353_);
v_res_4357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4351_, v_sz_boxed_4355_, v_i_boxed_4356_, v_b_4354_);
lean_dec_ref(v_b_4354_);
lean_dec_ref(v_as_4351_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4358_, size_t v_sz_4359_, size_t v_i_4360_, lean_object* v_b_4361_){
_start:
{
lean_object* v_a_4363_; uint8_t v___x_4367_; 
v___x_4367_ = lean_usize_dec_lt(v_i_4360_, v_sz_4359_);
if (v___x_4367_ == 0)
{
lean_inc_ref(v_b_4361_);
return v_b_4361_;
}
else
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v_a_4370_; 
v___x_4368_ = lean_box(0);
v___x_4369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4370_ = lean_array_uget(v_as_4358_, v_i_4360_);
if (lean_obj_tag(v_a_4370_) == 1)
{
lean_object* v_i_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4405_; 
v_i_4371_ = lean_ctor_get(v_a_4370_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_a_4370_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; 
v_unused_4406_ = lean_ctor_get(v_a_4370_, 1);
lean_dec(v_unused_4406_);
v___x_4373_ = v_a_4370_;
v_isShared_4374_ = v_isSharedCheck_4405_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_i_4371_);
lean_dec(v_a_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4405_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
if (lean_obj_tag(v_i_4371_) == 10)
{
lean_object* v_i_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4404_; 
v_i_4375_ = lean_ctor_get(v_i_4371_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_i_4371_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4377_ = v_i_4371_;
v_isShared_4378_ = v_isSharedCheck_4404_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_i_4375_);
lean_dec(v_i_4371_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4404_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v_stx_4379_; lean_object* v_value_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4403_; 
v_stx_4379_ = lean_ctor_get(v_i_4375_, 0);
v_value_4380_ = lean_ctor_get(v_i_4375_, 1);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_i_4375_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4382_ = v_i_4375_;
v_isShared_4383_ = v_isSharedCheck_4403_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_value_4380_);
lean_inc(v_stx_4379_);
lean_dec(v_i_4375_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4403_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4385_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4380_, v___x_4384_);
lean_dec(v_value_4380_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_del_object(v___x_4382_);
lean_dec(v_stx_4379_);
lean_del_object(v___x_4377_);
lean_del_object(v___x_4373_);
v_a_4363_ = v___x_4369_;
goto v___jp_4362_;
}
else
{
lean_object* v_val_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4402_; 
v_val_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4402_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_val_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4402_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 1, v_val_4386_);
v___x_4391_ = v___x_4382_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_stx_4379_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_val_4386_);
v___x_4391_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4393_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4391_);
v___x_4393_ = v___x_4388_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4395_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 1);
lean_ctor_set(v___x_4377_, 0, v___x_4393_);
v___x_4395_ = v___x_4377_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4397_; 
if (v_isShared_4374_ == 0)
{
lean_ctor_set_tag(v___x_4373_, 0);
lean_ctor_set(v___x_4373_, 1, v___x_4368_);
lean_ctor_set(v___x_4373_, 0, v___x_4395_);
v___x_4397_ = v___x_4373_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v___x_4368_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
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
lean_del_object(v___x_4373_);
lean_dec_ref(v_i_4371_);
v_a_4363_ = v___x_4369_;
goto v___jp_4362_;
}
}
}
else
{
lean_dec(v_a_4370_);
v_a_4363_ = v___x_4369_;
goto v___jp_4362_;
}
}
v___jp_4362_:
{
size_t v___x_4364_; size_t v___x_4365_; lean_object* v___x_4366_; 
v___x_4364_ = ((size_t)1ULL);
v___x_4365_ = lean_usize_add(v_i_4360_, v___x_4364_);
v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4358_, v_sz_4359_, v___x_4365_, v_a_4363_);
return v___x_4366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4407_, lean_object* v_sz_4408_, lean_object* v_i_4409_, lean_object* v_b_4410_){
_start:
{
size_t v_sz_boxed_4411_; size_t v_i_boxed_4412_; lean_object* v_res_4413_; 
v_sz_boxed_4411_ = lean_unbox_usize(v_sz_4408_);
lean_dec(v_sz_4408_);
v_i_boxed_4412_ = lean_unbox_usize(v_i_4409_);
lean_dec(v_i_4409_);
v_res_4413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4407_, v_sz_boxed_4411_, v_i_boxed_4412_, v_b_4410_);
lean_dec_ref(v_b_4410_);
lean_dec_ref(v_as_4407_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4414_){
_start:
{
if (lean_obj_tag(v_x_4414_) == 0)
{
lean_object* v_cs_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; size_t v_sz_4418_; size_t v___x_4419_; lean_object* v___x_4420_; lean_object* v_fst_4421_; 
v_cs_4415_ = lean_ctor_get(v_x_4414_, 0);
v___x_4416_ = lean_box(0);
v___x_4417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4418_ = lean_array_size(v_cs_4415_);
v___x_4419_ = ((size_t)0ULL);
v___x_4420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4415_, v_sz_4418_, v___x_4419_, v___x_4417_);
v_fst_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_fst_4421_);
lean_dec_ref(v___x_4420_);
if (lean_obj_tag(v_fst_4421_) == 0)
{
return v___x_4416_;
}
else
{
lean_object* v_val_4422_; 
v_val_4422_ = lean_ctor_get(v_fst_4421_, 0);
lean_inc(v_val_4422_);
lean_dec_ref(v_fst_4421_);
return v_val_4422_;
}
}
else
{
lean_object* v_vs_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; size_t v_sz_4426_; size_t v___x_4427_; lean_object* v___x_4428_; lean_object* v_fst_4429_; 
v_vs_4423_ = lean_ctor_get(v_x_4414_, 0);
v___x_4424_ = lean_box(0);
v___x_4425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4426_ = lean_array_size(v_vs_4423_);
v___x_4427_ = ((size_t)0ULL);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4423_, v_sz_4426_, v___x_4427_, v___x_4425_);
v_fst_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_fst_4429_);
lean_dec_ref(v___x_4428_);
if (lean_obj_tag(v_fst_4429_) == 0)
{
return v___x_4424_;
}
else
{
lean_object* v_val_4430_; 
v_val_4430_ = lean_ctor_get(v_fst_4429_, 0);
lean_inc(v_val_4430_);
lean_dec_ref(v_fst_4429_);
return v_val_4430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4431_, size_t v_sz_4432_, size_t v_i_4433_, lean_object* v_b_4434_){
_start:
{
uint8_t v___x_4435_; 
v___x_4435_ = lean_usize_dec_lt(v_i_4433_, v_sz_4432_);
if (v___x_4435_ == 0)
{
lean_inc_ref(v_b_4434_);
return v_b_4434_;
}
else
{
lean_object* v___x_4436_; lean_object* v_a_4437_; lean_object* v___x_4438_; 
v___x_4436_ = lean_box(0);
v_a_4437_ = lean_array_uget_borrowed(v_as_4431_, v_i_4433_);
v___x_4438_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4437_);
if (lean_obj_tag(v___x_4438_) == 1)
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
v___x_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
lean_ctor_set(v___x_4440_, 1, v___x_4436_);
return v___x_4440_;
}
else
{
lean_object* v___x_4441_; size_t v___x_4442_; size_t v___x_4443_; 
lean_dec(v___x_4438_);
v___x_4441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4442_ = ((size_t)1ULL);
v___x_4443_ = lean_usize_add(v_i_4433_, v___x_4442_);
v_i_4433_ = v___x_4443_;
v_b_4434_ = v___x_4441_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4445_, lean_object* v_sz_4446_, lean_object* v_i_4447_, lean_object* v_b_4448_){
_start:
{
size_t v_sz_boxed_4449_; size_t v_i_boxed_4450_; lean_object* v_res_4451_; 
v_sz_boxed_4449_ = lean_unbox_usize(v_sz_4446_);
lean_dec(v_sz_4446_);
v_i_boxed_4450_ = lean_unbox_usize(v_i_4447_);
lean_dec(v_i_4447_);
v_res_4451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4445_, v_sz_boxed_4449_, v_i_boxed_4450_, v_b_4448_);
lean_dec_ref(v_b_4448_);
lean_dec_ref(v_as_4445_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4452_);
lean_dec_ref(v_x_4452_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4454_){
_start:
{
lean_object* v_root_4455_; lean_object* v_tail_4456_; lean_object* v___x_4457_; 
v_root_4455_ = lean_ctor_get(v_t_4454_, 0);
v_tail_4456_ = lean_ctor_get(v_t_4454_, 1);
v___x_4457_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4455_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; size_t v_sz_4459_; size_t v___x_4460_; lean_object* v___x_4461_; lean_object* v_fst_4462_; 
v___x_4458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4459_ = lean_array_size(v_tail_4456_);
v___x_4460_ = ((size_t)0ULL);
v___x_4461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4456_, v_sz_4459_, v___x_4460_, v___x_4458_);
v_fst_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_fst_4462_);
lean_dec_ref(v___x_4461_);
if (lean_obj_tag(v_fst_4462_) == 0)
{
return v___x_4457_;
}
else
{
lean_object* v_val_4463_; 
v_val_4463_ = lean_ctor_get(v_fst_4462_, 0);
lean_inc(v_val_4463_);
lean_dec_ref(v_fst_4462_);
return v_val_4463_;
}
}
else
{
return v___x_4457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4464_);
lean_dec_ref(v_t_4464_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4480_, lean_object* v_a_4481_){
_start:
{
if (lean_obj_tag(v_node_4480_) == 1)
{
lean_object* v_children_4483_; lean_object* v_res_4484_; 
v_children_4483_ = lean_ctor_get(v_node_4480_, 1);
v_res_4484_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4483_);
if (lean_obj_tag(v_res_4484_) == 1)
{
lean_object* v_val_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4522_; 
v_val_4485_ = lean_ctor_get(v_res_4484_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_res_4484_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4487_ = v_res_4484_;
v_isShared_4488_ = v_isSharedCheck_4522_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_val_4485_);
lean_dec(v_res_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4522_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v_fst_4489_; lean_object* v_snd_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4521_; 
v_fst_4489_ = lean_ctor_get(v_val_4485_, 0);
v_snd_4490_ = lean_ctor_get(v_val_4485_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_val_4485_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4492_ = v_val_4485_;
v_isShared_4493_ = v_isSharedCheck_4521_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_snd_4490_);
lean_inc(v_fst_4489_);
lean_dec(v_val_4485_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4521_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4520_; 
v___x_4494_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4481_);
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4520_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4520_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; uint8_t v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___y_4507_; lean_object* v___x_4509_; 
v___x_4499_ = lean_box(0);
v___x_4500_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4501_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4502_ = 1;
v___x_4503_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4504_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4505_ = l_Lean_Syntax_getPos_x3f(v_fst_4489_, v___x_4502_);
v___x_4506_ = lean_box(v___x_4502_);
v___y_4507_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4507_, 0, v___x_4505_);
lean_closure_set(v___y_4507_, 1, v_fst_4489_);
lean_closure_set(v___y_4507_, 2, v___x_4506_);
lean_closure_set(v___y_4507_, 3, v_a_4495_);
lean_closure_set(v___y_4507_, 4, v___x_4499_);
lean_closure_set(v___y_4507_, 5, v___x_4500_);
lean_closure_set(v___y_4507_, 6, v___x_4501_);
lean_closure_set(v___y_4507_, 7, v___x_4499_);
lean_closure_set(v___y_4507_, 8, v___x_4503_);
lean_closure_set(v___y_4507_, 9, v___x_4499_);
lean_closure_set(v___y_4507_, 10, v___x_4499_);
lean_closure_set(v___y_4507_, 11, v___x_4499_);
lean_closure_set(v___y_4507_, 12, v_snd_4490_);
lean_closure_set(v___y_4507_, 13, v___x_4504_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___y_4507_);
v___x_4509_ = v___x_4487_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___y_4507_);
v___x_4509_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4511_; 
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 1, v___x_4509_);
lean_ctor_set(v___x_4492_, 0, v___x_4504_);
v___x_4511_ = v___x_4492_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4504_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v___x_4509_);
v___x_4511_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4516_; 
v___x_4512_ = lean_unsigned_to_nat(1u);
v___x_4513_ = lean_mk_empty_array_with_capacity(v___x_4512_);
v___x_4514_ = lean_array_push(v___x_4513_, v___x_4511_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4514_);
v___x_4516_ = v___x_4497_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_dec(v_res_4484_);
v___x_4523_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
return v___x_4524_;
}
}
else
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4527_, v_a_4528_);
lean_dec_ref(v_a_4528_);
lean_dec_ref(v_node_4527_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4531_, lean_object* v_x_4532_, lean_object* v_x_4533_, lean_object* v_node_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4534_, v_a_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4538_, lean_object* v_x_4539_, lean_object* v_x_4540_, lean_object* v_node_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4538_, v_x_4539_, v_x_4540_, v_node_4541_, v_a_4542_);
lean_dec_ref(v_a_4542_);
lean_dec_ref(v_node_4541_);
lean_dec_ref(v_x_4540_);
lean_dec_ref(v_x_4539_);
lean_dec_ref(v_x_4538_);
return v_res_4544_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4545_, lean_object* v_inst_4546_, lean_object* v_R_4547_, lean_object* v_a_4548_, uint8_t v_b_4549_, lean_object* v_c_4550_){
_start:
{
uint8_t v___x_4551_; 
v___x_4551_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4545_, v_a_4548_, v_b_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4552_, lean_object* v_inst_4553_, lean_object* v_R_4554_, lean_object* v_a_4555_, lean_object* v_b_4556_, lean_object* v_c_4557_){
_start:
{
uint8_t v_b_boxed_4558_; uint8_t v_res_4559_; lean_object* v_r_4560_; 
v_b_boxed_4558_ = lean_unbox(v_b_4556_);
v_res_4559_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4552_, v_inst_4553_, v_R_4554_, v_a_4555_, v_b_boxed_4558_, v_c_4557_);
lean_dec_ref(v_s_4552_);
v_r_4560_ = lean_box(v_res_4559_);
return v_r_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_(){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4566_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_));
v___x_4567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4568_ = l_Lean_CodeAction_insertBuiltin(v___x_4566_, v___x_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365____boxed(lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_();
return v_res_4570_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4573_ = lean_string_utf8_byte_size(v___x_4572_);
return v___x_4573_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; 
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4576_ = lean_nat_dec_eq(v___x_4575_, v___x_4574_);
return v___x_4576_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4577_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4578_ = lean_unsigned_to_nat(0u);
v___x_4579_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v___x_4578_);
lean_ctor_set(v___x_4580_, 2, v___x_4577_);
return v___x_4580_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4582_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4581_);
return v___x_4582_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4583_ = lean_unsigned_to_nat(0u);
v___x_4584_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4585_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4586_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
lean_ctor_set(v___x_4586_, 1, v___x_4584_);
lean_ctor_set(v___x_4586_, 2, v___x_4583_);
lean_ctor_set(v___x_4586_, 3, v___x_4583_);
return v___x_4586_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4587_){
_start:
{
lean_object* v___y_4589_; uint8_t v___x_4592_; 
v___x_4592_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4589_ = v___x_4593_;
goto v___jp_4588_;
}
else
{
lean_object* v___x_4594_; 
v___x_4594_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4589_ = v___x_4594_;
goto v___jp_4588_;
}
v___jp_4588_:
{
uint8_t v___x_4590_; uint8_t v___x_4591_; 
v___x_4590_ = 0;
lean_inc(v___y_4589_);
v___x_4591_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4587_, v___y_4589_, v___x_4590_);
return v___x_4591_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4595_){
_start:
{
uint8_t v_res_4596_; lean_object* v_r_4597_; 
v_res_4596_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4595_);
lean_dec_ref(v_s_4595_);
v_r_4597_ = lean_box(v_res_4596_);
return v_r_4597_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4598_, lean_object* v_as_x27_4599_, uint8_t v_b_4600_){
_start:
{
if (lean_obj_tag(v_as_x27_4599_) == 0)
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_box(v_b_4600_);
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
else
{
lean_object* v_head_4604_; uint8_t v_isSilent_4605_; 
v_head_4604_ = lean_ctor_get(v_as_x27_4599_, 0);
v_isSilent_4605_ = lean_ctor_get_uint8(v_head_4604_, sizeof(void*)*5 + 2);
if (v_isSilent_4605_ == 0)
{
lean_object* v_tail_4606_; lean_object* v_data_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v_tail_4606_ = lean_ctor_get(v_as_x27_4599_, 1);
v_data_4607_ = lean_ctor_get(v_head_4604_, 4);
lean_inc(v_data_4607_);
v___x_4608_ = l_Lean_MessageData_toString(v_data_4607_);
v___x_4609_ = lean_unsigned_to_nat(0u);
v___x_4610_ = lean_string_utf8_byte_size(v___x_4608_);
v___x_4611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4608_);
lean_ctor_set(v___x_4611_, 1, v___x_4609_);
lean_ctor_set(v___x_4611_, 2, v___x_4610_);
v___x_4612_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4611_);
lean_dec_ref(v___x_4611_);
if (v___x_4612_ == 0)
{
v_as_x27_4599_ = v_tail_4606_;
goto _start;
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = lean_box(v_foundPanic_4598_);
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
}
else
{
lean_object* v_tail_4616_; 
v_tail_4616_ = lean_ctor_get(v_as_x27_4599_, 1);
v_as_x27_4599_ = v_tail_4616_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4618_, lean_object* v_as_x27_4619_, lean_object* v_b_4620_, lean_object* v___y_4621_){
_start:
{
uint8_t v_foundPanic_boxed_4622_; uint8_t v_b_boxed_4623_; lean_object* v_res_4624_; 
v_foundPanic_boxed_4622_ = lean_unbox(v_foundPanic_4618_);
v_b_boxed_4623_ = lean_unbox(v_b_4620_);
v_res_4624_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4622_, v_as_x27_4619_, v_b_boxed_4623_);
lean_dec(v_as_x27_4619_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4625_, uint8_t v_severity_4626_, uint8_t v_isSilent_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Lean_Elab_Command_getRef___redArg(v___y_4628_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref(v___x_4631_);
v___x_4633_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4632_, v_msgData_4625_, v_severity_4626_, v_isSilent_4627_, v___y_4628_, v___y_4629_);
lean_dec(v_a_4632_);
return v___x_4633_;
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_dec_ref(v_msgData_4625_);
v_a_4634_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4631_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4631_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4642_, lean_object* v_severity_4643_, lean_object* v_isSilent_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
uint8_t v_severity_boxed_4648_; uint8_t v_isSilent_boxed_4649_; lean_object* v_res_4650_; 
v_severity_boxed_4648_ = lean_unbox(v_severity_4643_);
v_isSilent_boxed_4649_ = lean_unbox(v_isSilent_4644_);
v_res_4650_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4642_, v_severity_boxed_4648_, v_isSilent_boxed_4649_, v___y_4645_, v___y_4646_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
uint8_t v___x_4655_; uint8_t v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = 2;
v___x_4656_ = 0;
v___x_4657_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4651_, v___x_4655_, v___x_4656_, v___y_4652_, v___y_4653_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
return v_res_4662_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4671_ = l_Lean_MessageData_ofFormat(v___x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v___x_4676_; uint8_t v_foundPanic_4677_; 
v___x_4676_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4672_);
v_foundPanic_4677_ = l_Lean_Syntax_isOfKind(v_x_4672_, v___x_4676_);
if (v_foundPanic_4677_ == 0)
{
lean_object* v___x_4678_; 
lean_dec(v_x_4672_);
v___x_4678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4678_;
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = lean_unsigned_to_nat(2u);
v___x_4680_ = l_Lean_Syntax_getArg(v_x_4672_, v___x_4679_);
lean_dec(v_x_4672_);
v___x_4681_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4680_, v_a_4673_, v_a_4674_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; uint8_t v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4740_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref(v___x_4681_);
v___x_4683_ = 0;
v___x_4684_ = l_Lean_MessageLog_toList(v_a_4682_);
v___x_4685_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4677_, v___x_4684_, v___x_4683_);
lean_dec(v___x_4684_);
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4688_ = v___x_4685_;
v_isShared_4689_ = v_isSharedCheck_4740_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4685_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4740_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
uint8_t v___x_4690_; 
v___x_4690_ = lean_unbox(v_a_4686_);
lean_dec(v_a_4686_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; lean_object* v_env_4692_; lean_object* v_scopes_4693_; lean_object* v_usedQuotCtxts_4694_; lean_object* v_nextMacroScope_4695_; lean_object* v_maxRecDepth_4696_; lean_object* v_ngen_4697_; lean_object* v_auxDeclNGen_4698_; lean_object* v_infoState_4699_; lean_object* v_traceState_4700_; lean_object* v_snapshotTasks_4701_; lean_object* v_newDecls_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4712_; 
lean_del_object(v___x_4688_);
v___x_4691_ = lean_st_ref_take(v_a_4674_);
v_env_4692_ = lean_ctor_get(v___x_4691_, 0);
v_scopes_4693_ = lean_ctor_get(v___x_4691_, 2);
v_usedQuotCtxts_4694_ = lean_ctor_get(v___x_4691_, 3);
v_nextMacroScope_4695_ = lean_ctor_get(v___x_4691_, 4);
v_maxRecDepth_4696_ = lean_ctor_get(v___x_4691_, 5);
v_ngen_4697_ = lean_ctor_get(v___x_4691_, 6);
v_auxDeclNGen_4698_ = lean_ctor_get(v___x_4691_, 7);
v_infoState_4699_ = lean_ctor_get(v___x_4691_, 8);
v_traceState_4700_ = lean_ctor_get(v___x_4691_, 9);
v_snapshotTasks_4701_ = lean_ctor_get(v___x_4691_, 10);
v_newDecls_4702_ = lean_ctor_get(v___x_4691_, 11);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4712_ == 0)
{
lean_object* v_unused_4713_; 
v_unused_4713_ = lean_ctor_get(v___x_4691_, 1);
lean_dec(v_unused_4713_);
v___x_4704_ = v___x_4691_;
v_isShared_4705_ = v_isSharedCheck_4712_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_newDecls_4702_);
lean_inc(v_snapshotTasks_4701_);
lean_inc(v_traceState_4700_);
lean_inc(v_infoState_4699_);
lean_inc(v_auxDeclNGen_4698_);
lean_inc(v_ngen_4697_);
lean_inc(v_maxRecDepth_4696_);
lean_inc(v_nextMacroScope_4695_);
lean_inc(v_usedQuotCtxts_4694_);
lean_inc(v_scopes_4693_);
lean_inc(v_env_4692_);
lean_dec(v___x_4691_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4712_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 1, v_a_4682_);
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_env_4692_);
lean_ctor_set(v_reuseFailAlloc_4711_, 1, v_a_4682_);
lean_ctor_set(v_reuseFailAlloc_4711_, 2, v_scopes_4693_);
lean_ctor_set(v_reuseFailAlloc_4711_, 3, v_usedQuotCtxts_4694_);
lean_ctor_set(v_reuseFailAlloc_4711_, 4, v_nextMacroScope_4695_);
lean_ctor_set(v_reuseFailAlloc_4711_, 5, v_maxRecDepth_4696_);
lean_ctor_set(v_reuseFailAlloc_4711_, 6, v_ngen_4697_);
lean_ctor_set(v_reuseFailAlloc_4711_, 7, v_auxDeclNGen_4698_);
lean_ctor_set(v_reuseFailAlloc_4711_, 8, v_infoState_4699_);
lean_ctor_set(v_reuseFailAlloc_4711_, 9, v_traceState_4700_);
lean_ctor_set(v_reuseFailAlloc_4711_, 10, v_snapshotTasks_4701_);
lean_ctor_set(v_reuseFailAlloc_4711_, 11, v_newDecls_4702_);
v___x_4707_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_st_ref_set(v_a_4674_, v___x_4707_);
v___x_4709_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4710_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4709_, v_a_4673_, v_a_4674_);
return v___x_4710_;
}
}
}
else
{
lean_object* v___x_4714_; lean_object* v_env_4715_; lean_object* v_scopes_4716_; lean_object* v_usedQuotCtxts_4717_; lean_object* v_nextMacroScope_4718_; lean_object* v_maxRecDepth_4719_; lean_object* v_ngen_4720_; lean_object* v_auxDeclNGen_4721_; lean_object* v_infoState_4722_; lean_object* v_traceState_4723_; lean_object* v_snapshotTasks_4724_; lean_object* v_newDecls_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4738_; 
lean_dec(v_a_4682_);
v___x_4714_ = lean_st_ref_take(v_a_4674_);
v_env_4715_ = lean_ctor_get(v___x_4714_, 0);
v_scopes_4716_ = lean_ctor_get(v___x_4714_, 2);
v_usedQuotCtxts_4717_ = lean_ctor_get(v___x_4714_, 3);
v_nextMacroScope_4718_ = lean_ctor_get(v___x_4714_, 4);
v_maxRecDepth_4719_ = lean_ctor_get(v___x_4714_, 5);
v_ngen_4720_ = lean_ctor_get(v___x_4714_, 6);
v_auxDeclNGen_4721_ = lean_ctor_get(v___x_4714_, 7);
v_infoState_4722_ = lean_ctor_get(v___x_4714_, 8);
v_traceState_4723_ = lean_ctor_get(v___x_4714_, 9);
v_snapshotTasks_4724_ = lean_ctor_get(v___x_4714_, 10);
v_newDecls_4725_ = lean_ctor_get(v___x_4714_, 11);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4738_ == 0)
{
lean_object* v_unused_4739_; 
v_unused_4739_ = lean_ctor_get(v___x_4714_, 1);
lean_dec(v_unused_4739_);
v___x_4727_ = v___x_4714_;
v_isShared_4728_ = v_isSharedCheck_4738_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_newDecls_4725_);
lean_inc(v_snapshotTasks_4724_);
lean_inc(v_traceState_4723_);
lean_inc(v_infoState_4722_);
lean_inc(v_auxDeclNGen_4721_);
lean_inc(v_ngen_4720_);
lean_inc(v_maxRecDepth_4719_);
lean_inc(v_nextMacroScope_4718_);
lean_inc(v_usedQuotCtxts_4717_);
lean_inc(v_scopes_4716_);
lean_inc(v_env_4715_);
lean_dec(v___x_4714_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4738_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4729_; lean_object* v___x_4731_; 
v___x_4729_ = l_Lean_MessageLog_empty;
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 1, v___x_4729_);
v___x_4731_ = v___x_4727_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_env_4715_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_scopes_4716_);
lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_usedQuotCtxts_4717_);
lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_nextMacroScope_4718_);
lean_ctor_set(v_reuseFailAlloc_4737_, 5, v_maxRecDepth_4719_);
lean_ctor_set(v_reuseFailAlloc_4737_, 6, v_ngen_4720_);
lean_ctor_set(v_reuseFailAlloc_4737_, 7, v_auxDeclNGen_4721_);
lean_ctor_set(v_reuseFailAlloc_4737_, 8, v_infoState_4722_);
lean_ctor_set(v_reuseFailAlloc_4737_, 9, v_traceState_4723_);
lean_ctor_set(v_reuseFailAlloc_4737_, 10, v_snapshotTasks_4724_);
lean_ctor_set(v_reuseFailAlloc_4737_, 11, v_newDecls_4725_);
v___x_4731_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4735_; 
v___x_4732_ = lean_st_ref_set(v_a_4674_, v___x_4731_);
v___x_4733_ = lean_box(0);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v___x_4733_);
v___x_4735_ = v___x_4688_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4733_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
v_a_4741_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4681_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4681_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4749_, v_a_4750_, v_a_4751_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4754_, lean_object* v_as_4755_, lean_object* v_as_x27_4756_, uint8_t v_b_4757_, lean_object* v_a_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4754_, v_as_x27_4756_, v_b_4757_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4763_, lean_object* v_as_4764_, lean_object* v_as_x27_4765_, lean_object* v_b_4766_, lean_object* v_a_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
uint8_t v_foundPanic_boxed_4771_; uint8_t v_b_boxed_4772_; lean_object* v_res_4773_; 
v_foundPanic_boxed_4771_ = lean_unbox(v_foundPanic_4763_);
v_b_boxed_4772_ = lean_unbox(v_b_4766_);
v_res_4773_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4771_, v_as_4764_, v_as_x27_4765_, v_b_boxed_4772_, v_a_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec(v_as_x27_4765_);
lean_dec(v_as_4764_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4782_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4783_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4784_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4785_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4786_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4782_, v___x_4783_, v___x_4784_, v___x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4788_;
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
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_();
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
