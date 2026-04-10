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
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_a_11567__boxed_576_; uint8_t v_res_577_; lean_object* v_r_578_; 
v_a_11567__boxed_576_ = lean_unbox(v_a_574_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_572_, v_snd_573_, v_a_11567__boxed_576_, v___y_575_);
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
uint8_t v___x_12442__boxed_1036_; size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; lean_object* v_res_1039_; 
v___x_12442__boxed_1036_ = lean_unbox(v___x_1031_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1034_);
lean_dec(v_stop_1034_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_12442__boxed_1036_, v_as_1032_, v_i_boxed_1037_, v_stop_boxed_1038_, v_b_1035_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_as_1579_, lean_object* v_lo_1580_, lean_object* v_hi_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_lt(v_lo_1580_, v_hi_1581_);
if (v___x_1582_ == 0)
{
lean_dec(v_lo_1580_);
return v_as_1579_;
}
else
{
lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v_fst_1585_; lean_object* v_snd_1586_; uint8_t v___x_1587_; 
v___f_1583_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___closed__0));
lean_inc(v_lo_1580_);
v___x_1584_ = l_Array_qpartition___redArg(v_as_1579_, v___f_1583_, v_lo_1580_, v_hi_1581_);
v_fst_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_fst_1585_);
v_snd_1586_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_snd_1586_);
lean_dec_ref(v___x_1584_);
v___x_1587_ = lean_nat_dec_le(v_hi_1581_, v_fst_1585_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_snd_1586_, v_lo_1580_, v_fst_1585_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_nat_add(v_fst_1585_, v___x_1589_);
lean_dec(v_fst_1585_);
v_as_1579_ = v___x_1588_;
v_lo_1580_ = v___x_1590_;
goto _start;
}
else
{
lean_dec(v_fst_1585_);
lean_dec(v_lo_1580_);
return v_snd_1586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_as_1592_, lean_object* v_lo_1593_, lean_object* v_hi_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_as_1592_, v_lo_1593_, v_hi_1594_);
lean_dec(v_hi_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1596_, lean_object* v_msgs_1597_){
_start:
{
if (v_mode_1596_ == 0)
{
return v_msgs_1597_;
}
else
{
lean_object* v___x_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1598_ = lean_array_mk(v_msgs_1597_);
v___x_1604_ = lean_array_get_size(v___x_1598_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_nat_dec_eq(v___x_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___y_1610_; uint8_t v___x_1612_; 
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = lean_nat_sub(v___x_1604_, v___x_1607_);
v___x_1612_ = lean_nat_dec_le(v___x_1605_, v___x_1608_);
if (v___x_1612_ == 0)
{
lean_inc(v___x_1608_);
v___y_1610_ = v___x_1608_;
goto v___jp_1609_;
}
else
{
v___y_1610_ = v___x_1605_;
goto v___jp_1609_;
}
v___jp_1609_:
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_nat_dec_le(v___y_1610_, v___x_1608_);
if (v___x_1611_ == 0)
{
lean_dec(v___x_1608_);
lean_inc(v___y_1610_);
v___y_1600_ = v___y_1610_;
v___y_1601_ = v___y_1610_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___y_1610_;
v___y_1601_ = v___x_1608_;
goto v___jp_1599_;
}
}
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_array_to_list(v___x_1598_);
return v___x_1613_;
}
v___jp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1598_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
v___x_1603_ = lean_array_to_list(v___x_1602_);
return v___x_1603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1614_, lean_object* v_msgs_1615_){
_start:
{
uint8_t v_mode_boxed_1616_; lean_object* v_res_1617_; 
v_mode_boxed_1616_ = lean_unbox(v_mode_1614_);
v_res_1617_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1616_, v_msgs_1615_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1618_, lean_object* v_as_1619_, lean_object* v_lo_1620_, lean_object* v_hi_1621_, lean_object* v_w_1622_, lean_object* v_hlo_1623_, lean_object* v_hhi_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_as_1619_, v_lo_1620_, v_hi_1621_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1626_, lean_object* v_as_1627_, lean_object* v_lo_1628_, lean_object* v_hi_1629_, lean_object* v_w_1630_, lean_object* v_hlo_1631_, lean_object* v_hhi_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1626_, v_as_1627_, v_lo_1628_, v_hi_1629_, v_w_1630_, v_hlo_1631_, v_hhi_1632_);
lean_dec(v_hi_1629_);
lean_dec(v_n_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1634_, size_t v_i_1635_, size_t v_stop_1636_, lean_object* v_b_1637_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_usize_dec_eq(v_i_1635_, v_stop_1636_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v_diagnostics_1640_; lean_object* v_msgLog_1641_; lean_object* v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; 
v___x_1639_ = lean_array_uget_borrowed(v_as_1634_, v_i_1635_);
v_diagnostics_1640_ = lean_ctor_get(v___x_1639_, 1);
v_msgLog_1641_ = lean_ctor_get(v_diagnostics_1640_, 0);
lean_inc_ref(v_msgLog_1641_);
v___x_1642_ = l_Lean_MessageLog_append(v_b_1637_, v_msgLog_1641_);
v___x_1643_ = ((size_t)1ULL);
v___x_1644_ = lean_usize_add(v_i_1635_, v___x_1643_);
v_i_1635_ = v___x_1644_;
v_b_1637_ = v___x_1642_;
goto _start;
}
else
{
return v_b_1637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1646_, lean_object* v_i_1647_, lean_object* v_stop_1648_, lean_object* v_b_1649_){
_start:
{
size_t v_i_boxed_1650_; size_t v_stop_boxed_1651_; lean_object* v_res_1652_; 
v_i_boxed_1650_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_stop_boxed_1651_ = lean_unbox_usize(v_stop_1648_);
lean_dec(v_stop_1648_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1646_, v_i_boxed_1650_, v_stop_boxed_1651_, v_b_1649_);
lean_dec_ref(v_as_1646_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1653_, size_t v_i_1654_, size_t v_stop_1655_, lean_object* v_b_1656_){
_start:
{
lean_object* v___y_1658_; uint8_t v___x_1662_; 
v___x_1662_ = lean_usize_dec_eq(v_i_1654_, v_stop_1655_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1663_ = lean_array_uget_borrowed(v_as_1653_, v_i_1654_);
v___x_1664_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1663_);
v___x_1665_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1663_);
v___x_1666_ = l_Lean_Language_SnapshotTree_getAll(v___x_1665_);
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = lean_array_get_size(v___x_1666_);
v___x_1669_ = lean_nat_dec_lt(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_dec_ref(v___x_1666_);
v___x_1670_ = l_Lean_MessageLog_append(v_b_1656_, v___x_1664_);
v___y_1658_ = v___x_1670_;
goto v___jp_1657_;
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_nat_dec_le(v___x_1668_, v___x_1668_);
if (v___x_1671_ == 0)
{
if (v___x_1669_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v___x_1666_);
v___x_1672_ = l_Lean_MessageLog_append(v_b_1656_, v___x_1664_);
v___y_1658_ = v___x_1672_;
goto v___jp_1657_;
}
else
{
size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = lean_usize_of_nat(v___x_1668_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1666_, v___x_1673_, v___x_1674_, v___x_1664_);
lean_dec_ref(v___x_1666_);
v___x_1676_ = l_Lean_MessageLog_append(v_b_1656_, v___x_1675_);
v___y_1658_ = v___x_1676_;
goto v___jp_1657_;
}
}
else
{
size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = lean_usize_of_nat(v___x_1668_);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1666_, v___x_1677_, v___x_1678_, v___x_1664_);
lean_dec_ref(v___x_1666_);
v___x_1680_ = l_Lean_MessageLog_append(v_b_1656_, v___x_1679_);
v___y_1658_ = v___x_1680_;
goto v___jp_1657_;
}
}
}
else
{
return v_b_1656_;
}
v___jp_1657_:
{
size_t v___x_1659_; size_t v___x_1660_; 
v___x_1659_ = ((size_t)1ULL);
v___x_1660_ = lean_usize_add(v_i_1654_, v___x_1659_);
v_i_1654_ = v___x_1660_;
v_b_1656_ = v___y_1658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1681_, lean_object* v_i_1682_, lean_object* v_stop_1683_, lean_object* v_b_1684_){
_start:
{
size_t v_i_boxed_1685_; size_t v_stop_boxed_1686_; lean_object* v_res_1687_; 
v_i_boxed_1685_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_stop_boxed_1686_ = lean_unbox_usize(v_stop_1683_);
lean_dec(v_stop_1683_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1681_, v_i_boxed_1685_, v_stop_boxed_1686_, v_b_1684_);
lean_dec_ref(v_as_1681_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_fileName_1694_; lean_object* v_fileMap_1695_; lean_object* v_currRecDepth_1696_; lean_object* v_cmdPos_1697_; lean_object* v_macroStack_1698_; lean_object* v_quotContext_x3f_1699_; lean_object* v_currMacroScope_1700_; lean_object* v_ref_1701_; lean_object* v_cancelTk_x3f_1702_; uint8_t v_suppressElabErrors_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_fileName_1694_ = lean_ctor_get(v_a_1691_, 0);
v_fileMap_1695_ = lean_ctor_get(v_a_1691_, 1);
v_currRecDepth_1696_ = lean_ctor_get(v_a_1691_, 2);
v_cmdPos_1697_ = lean_ctor_get(v_a_1691_, 3);
v_macroStack_1698_ = lean_ctor_get(v_a_1691_, 4);
v_quotContext_x3f_1699_ = lean_ctor_get(v_a_1691_, 5);
v_currMacroScope_1700_ = lean_ctor_get(v_a_1691_, 6);
v_ref_1701_ = lean_ctor_get(v_a_1691_, 7);
v_cancelTk_x3f_1702_ = lean_ctor_get(v_a_1691_, 9);
v_suppressElabErrors_1703_ = lean_ctor_get_uint8(v_a_1691_, sizeof(void*)*10);
v___x_1704_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1702_);
lean_inc(v_ref_1701_);
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_x3f_1699_);
lean_inc(v_macroStack_1698_);
lean_inc(v_cmdPos_1697_);
lean_inc(v_currRecDepth_1696_);
lean_inc_ref(v_fileMap_1695_);
lean_inc_ref(v_fileName_1694_);
v___x_1705_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1705_, 0, v_fileName_1694_);
lean_ctor_set(v___x_1705_, 1, v_fileMap_1695_);
lean_ctor_set(v___x_1705_, 2, v_currRecDepth_1696_);
lean_ctor_set(v___x_1705_, 3, v_cmdPos_1697_);
lean_ctor_set(v___x_1705_, 4, v_macroStack_1698_);
lean_ctor_set(v___x_1705_, 5, v_quotContext_x3f_1699_);
lean_ctor_set(v___x_1705_, 6, v_currMacroScope_1700_);
lean_ctor_set(v___x_1705_, 7, v_ref_1701_);
lean_ctor_set(v___x_1705_, 8, v___x_1704_);
lean_ctor_set(v___x_1705_, 9, v_cancelTk_x3f_1702_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*10, v_suppressElabErrors_1703_);
v___x_1706_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1690_, v___x_1705_, v_a_1692_);
lean_dec_ref(v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1752_; 
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1706_, 0);
lean_dec(v_unused_1753_);
v___x_1708_ = v___x_1706_;
v_isShared_1709_ = v_isSharedCheck_1752_;
goto v_resetjp_1707_;
}
else
{
lean_dec(v___x_1706_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1752_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_messages_1712_; lean_object* v___y_1714_; lean_object* v_snapshotTasks_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1710_ = lean_st_ref_get(v_a_1692_);
v___x_1711_ = lean_st_ref_get(v_a_1692_);
v_messages_1712_ = lean_ctor_get(v___x_1710_, 1);
lean_inc_ref(v_messages_1712_);
lean_dec(v___x_1710_);
v_snapshotTasks_1740_ = lean_ctor_get(v___x_1711_, 10);
lean_inc_ref(v_snapshotTasks_1740_);
lean_dec(v___x_1711_);
v___x_1741_ = l_Lean_MessageLog_empty;
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_array_get_size(v_snapshotTasks_1740_);
v___x_1744_ = lean_nat_dec_lt(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_dec_ref(v_snapshotTasks_1740_);
v___y_1714_ = v___x_1741_;
goto v___jp_1713_;
}
else
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_le(v___x_1743_, v___x_1743_);
if (v___x_1745_ == 0)
{
if (v___x_1744_ == 0)
{
lean_dec_ref(v_snapshotTasks_1740_);
v___y_1714_ = v___x_1741_;
goto v___jp_1713_;
}
else
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = ((size_t)0ULL);
v___x_1747_ = lean_usize_of_nat(v___x_1743_);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1740_, v___x_1746_, v___x_1747_, v___x_1741_);
lean_dec_ref(v_snapshotTasks_1740_);
v___y_1714_ = v___x_1748_;
goto v___jp_1713_;
}
}
else
{
size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((size_t)0ULL);
v___x_1750_ = lean_usize_of_nat(v___x_1743_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1740_, v___x_1749_, v___x_1750_, v___x_1741_);
lean_dec_ref(v_snapshotTasks_1740_);
v___y_1714_ = v___x_1751_;
goto v___jp_1713_;
}
}
v___jp_1713_:
{
lean_object* v___x_1715_; lean_object* v_env_1716_; lean_object* v_messages_1717_; lean_object* v_scopes_1718_; lean_object* v_usedQuotCtxts_1719_; lean_object* v_nextMacroScope_1720_; lean_object* v_maxRecDepth_1721_; lean_object* v_ngen_1722_; lean_object* v_auxDeclNGen_1723_; lean_object* v_infoState_1724_; lean_object* v_traceState_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1738_; 
v___x_1715_ = lean_st_ref_take(v_a_1692_);
v_env_1716_ = lean_ctor_get(v___x_1715_, 0);
v_messages_1717_ = lean_ctor_get(v___x_1715_, 1);
v_scopes_1718_ = lean_ctor_get(v___x_1715_, 2);
v_usedQuotCtxts_1719_ = lean_ctor_get(v___x_1715_, 3);
v_nextMacroScope_1720_ = lean_ctor_get(v___x_1715_, 4);
v_maxRecDepth_1721_ = lean_ctor_get(v___x_1715_, 5);
v_ngen_1722_ = lean_ctor_get(v___x_1715_, 6);
v_auxDeclNGen_1723_ = lean_ctor_get(v___x_1715_, 7);
v_infoState_1724_ = lean_ctor_get(v___x_1715_, 8);
v_traceState_1725_ = lean_ctor_get(v___x_1715_, 9);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v___x_1715_, 10);
lean_dec(v_unused_1739_);
v___x_1727_ = v___x_1715_;
v_isShared_1728_ = v_isSharedCheck_1738_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_traceState_1725_);
lean_inc(v_infoState_1724_);
lean_inc(v_auxDeclNGen_1723_);
lean_inc(v_ngen_1722_);
lean_inc(v_maxRecDepth_1721_);
lean_inc(v_nextMacroScope_1720_);
lean_inc(v_usedQuotCtxts_1719_);
lean_inc(v_scopes_1718_);
lean_inc(v_messages_1717_);
lean_inc(v_env_1716_);
lean_dec(v___x_1715_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1738_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 10, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_env_1716_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_messages_1717_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_scopes_1718_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_usedQuotCtxts_1719_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_nextMacroScope_1720_);
lean_ctor_set(v_reuseFailAlloc_1737_, 5, v_maxRecDepth_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 6, v_ngen_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 7, v_auxDeclNGen_1723_);
lean_ctor_set(v_reuseFailAlloc_1737_, 8, v_infoState_1724_);
lean_ctor_set(v_reuseFailAlloc_1737_, 9, v_traceState_1725_);
lean_ctor_set(v_reuseFailAlloc_1737_, 10, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = lean_st_ref_set(v_a_1692_, v___x_1731_);
v___x_1733_ = l_Lean_MessageLog_append(v_messages_1712_, v___y_1714_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1733_);
v___x_1735_ = v___x_1708_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1706_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1706_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1767_, lean_object* v_opt_1768_){
_start:
{
lean_object* v_name_1769_; lean_object* v_defValue_1770_; lean_object* v_map_1771_; lean_object* v___x_1772_; 
v_name_1769_ = lean_ctor_get(v_opt_1768_, 0);
v_defValue_1770_ = lean_ctor_get(v_opt_1768_, 1);
v_map_1771_ = lean_ctor_get(v_opts_1767_, 0);
v___x_1772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1771_, v_name_1769_);
if (lean_obj_tag(v___x_1772_) == 0)
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_unbox(v_defValue_1770_);
return v___x_1773_;
}
else
{
lean_object* v_val_1774_; 
v_val_1774_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_val_1774_);
lean_dec_ref(v___x_1772_);
if (lean_obj_tag(v_val_1774_) == 1)
{
uint8_t v_v_1775_; 
v_v_1775_ = lean_ctor_get_uint8(v_val_1774_, 0);
lean_dec_ref(v_val_1774_);
return v_v_1775_;
}
else
{
uint8_t v___x_1776_; 
lean_dec(v_val_1774_);
v___x_1776_ = lean_unbox(v_defValue_1770_);
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1777_, lean_object* v_opt_1778_){
_start:
{
uint8_t v_res_1779_; lean_object* v_r_1780_; 
v_res_1779_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1777_, v_opt_1778_);
lean_dec_ref(v_opt_1778_);
lean_dec_ref(v_opts_1777_);
v_r_1780_ = lean_box(v_res_1779_);
return v_r_1780_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1785_);
lean_dec_ref(v_s_1785_);
return v_res_1786_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_box(1);
v___x_1788_ = l_Lean_MessageData_ofFormat(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1793_ = l_Lean_MessageData_ofFormat(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1794_, lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
return v_x_1794_;
}
else
{
lean_object* v_head_1796_; lean_object* v_tail_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1819_; 
v_head_1796_ = lean_ctor_get(v_x_1795_, 0);
v_tail_1797_ = lean_ctor_get(v_x_1795_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1799_ = v_x_1795_;
v_isShared_1800_ = v_isSharedCheck_1819_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_tail_1797_);
lean_inc(v_head_1796_);
lean_dec(v_x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1819_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_before_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1817_; 
v_before_1801_ = lean_ctor_get(v_head_1796_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_head_1796_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v_head_1796_, 1);
lean_dec(v_unused_1818_);
v___x_1803_ = v_head_1796_;
v_isShared_1804_ = v_isSharedCheck_1817_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_before_1801_);
lean_dec(v_head_1796_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1817_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 7);
lean_ctor_set(v___x_1803_, 1, v___x_1805_);
lean_ctor_set(v___x_1803_, 0, v_x_1794_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_x_1794_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 7);
lean_ctor_set(v___x_1799_, 1, v___x_1808_);
lean_ctor_set(v___x_1799_, 0, v___x_1807_);
v___x_1810_ = v___x_1799_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = l_Lean_MessageData_ofSyntax(v_before_1801_);
v___x_1812_ = l_Lean_indentD(v___x_1811_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1810_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v_x_1794_ = v___x_1813_;
v_x_1795_ = v_tail_1797_;
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
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1825_, lean_object* v_macroStack_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v_scopes_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_opts_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1829_ = lean_st_ref_get(v___y_1827_);
v_scopes_1830_ = lean_ctor_get(v___x_1829_, 2);
lean_inc(v_scopes_1830_);
lean_dec(v___x_1829_);
v___x_1831_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1832_ = l_List_head_x21___redArg(v___x_1831_, v_scopes_1830_);
lean_dec(v_scopes_1830_);
v_opts_1833_ = lean_ctor_get(v___x_1832_, 1);
lean_inc_ref(v_opts_1833_);
lean_dec(v___x_1832_);
v___x_1834_ = l_Lean_Elab_pp_macroStack;
v___x_1835_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1833_, v___x_1834_);
lean_dec_ref(v_opts_1833_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_dec(v_macroStack_1826_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_msgData_1825_);
return v___x_1836_;
}
else
{
if (lean_obj_tag(v_macroStack_1826_) == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v_msgData_1825_);
return v___x_1837_;
}
else
{
lean_object* v_head_1838_; lean_object* v_after_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1854_; 
v_head_1838_ = lean_ctor_get(v_macroStack_1826_, 0);
lean_inc(v_head_1838_);
v_after_1839_ = lean_ctor_get(v_head_1838_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_head_1838_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_head_1838_, 0);
lean_dec(v_unused_1855_);
v___x_1841_ = v_head_1838_;
v_isShared_1842_ = v_isSharedCheck_1854_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_after_1839_);
lean_dec(v_head_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1854_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 7);
lean_ctor_set(v___x_1841_, 1, v___x_1843_);
lean_ctor_set(v___x_1841_, 0, v_msgData_1825_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_msgData_1825_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_msgData_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1846_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = l_Lean_MessageData_ofSyntax(v_after_1839_);
v___x_1849_ = l_Lean_indentD(v___x_1848_);
v_msgData_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1850_, 0, v___x_1847_);
lean_ctor_set(v_msgData_1850_, 1, v___x_1849_);
v___x_1851_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1850_, v_macroStack_1826_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1856_, lean_object* v_macroStack_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1856_, v_macroStack_1857_, v___y_1858_);
lean_dec(v___y_1858_);
return v_res_1860_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
lean_ctor_set(v___x_1866_, 2, v___x_1865_);
lean_ctor_set(v___x_1866_, 3, v___x_1865_);
lean_ctor_set(v___x_1866_, 4, v___x_1864_);
lean_ctor_set(v___x_1866_, 5, v___x_1864_);
lean_ctor_set(v___x_1866_, 6, v___x_1864_);
lean_ctor_set(v___x_1866_, 7, v___x_1864_);
lean_ctor_set(v___x_1866_, 8, v___x_1864_);
lean_ctor_set(v___x_1866_, 9, v___x_1864_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_unsigned_to_nat(32u);
v___x_1868_ = lean_mk_empty_array_with_capacity(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1870_ = ((size_t)5ULL);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_unsigned_to_nat(32u);
v___x_1873_ = lean_mk_empty_array_with_capacity(v___x_1872_);
v___x_1874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1875_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
lean_ctor_set(v___x_1875_, 2, v___x_1871_);
lean_ctor_set(v___x_1875_, 3, v___x_1871_);
lean_ctor_set_usize(v___x_1875_, 4, v___x_1870_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = lean_box(1);
v___x_1877_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1878_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1877_);
lean_ctor_set(v___x_1879_, 2, v___x_1876_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; lean_object* v_env_1884_; lean_object* v___x_1885_; lean_object* v_scopes_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_opts_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1883_ = lean_st_ref_get(v___y_1881_);
v_env_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_ref(v_env_1884_);
lean_dec(v___x_1883_);
v___x_1885_ = lean_st_ref_get(v___y_1881_);
v_scopes_1886_ = lean_ctor_get(v___x_1885_, 2);
lean_inc(v_scopes_1886_);
lean_dec(v___x_1885_);
v___x_1887_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1888_ = l_List_head_x21___redArg(v___x_1887_, v_scopes_1886_);
lean_dec(v_scopes_1886_);
v_opts_1889_ = lean_ctor_get(v___x_1888_, 1);
lean_inc_ref(v_opts_1889_);
lean_dec(v___x_1888_);
v___x_1890_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1891_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1892_, 0, v_env_1884_);
lean_ctor_set(v___x_1892_, 1, v___x_1890_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
lean_ctor_set(v___x_1892_, 3, v_opts_1889_);
v___x_1893_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v_msgData_1880_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1895_, v___y_1896_);
lean_dec(v___y_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Elab_Command_getRef___redArg(v___y_1900_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v_macroStack_1905_; lean_object* v___x_1906_; lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v___x_1903_);
v_macroStack_1905_ = lean_ctor_get(v___y_1900_, 4);
v___x_1906_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1899_, v___y_1901_);
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
lean_inc_n(v_macroStack_1905_, 2);
v___x_1908_ = l_Lean_Elab_getBetterRef(v_a_1904_, v_macroStack_1905_);
lean_dec(v_a_1904_);
v___x_1909_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1907_, v_macroStack_1905_, v___y_1901_);
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1908_);
lean_ctor_set(v___x_1914_, 1, v_a_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 1);
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_msg_1899_);
v_a_1919_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1903_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1903_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Elab_Command_getRef___redArg(v___y_1934_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v_fileName_1939_; lean_object* v_fileMap_1940_; lean_object* v_currRecDepth_1941_; lean_object* v_cmdPos_1942_; lean_object* v_macroStack_1943_; lean_object* v_quotContext_x3f_1944_; lean_object* v_currMacroScope_1945_; lean_object* v_snap_x3f_1946_; lean_object* v_cancelTk_x3f_1947_; uint8_t v_suppressElabErrors_1948_; lean_object* v_ref_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v_fileName_1939_ = lean_ctor_get(v___y_1934_, 0);
v_fileMap_1940_ = lean_ctor_get(v___y_1934_, 1);
v_currRecDepth_1941_ = lean_ctor_get(v___y_1934_, 2);
v_cmdPos_1942_ = lean_ctor_get(v___y_1934_, 3);
v_macroStack_1943_ = lean_ctor_get(v___y_1934_, 4);
v_quotContext_x3f_1944_ = lean_ctor_get(v___y_1934_, 5);
v_currMacroScope_1945_ = lean_ctor_get(v___y_1934_, 6);
v_snap_x3f_1946_ = lean_ctor_get(v___y_1934_, 8);
v_cancelTk_x3f_1947_ = lean_ctor_get(v___y_1934_, 9);
v_suppressElabErrors_1948_ = lean_ctor_get_uint8(v___y_1934_, sizeof(void*)*10);
v_ref_1949_ = l_Lean_replaceRef(v_ref_1932_, v_a_1938_);
lean_dec(v_a_1938_);
lean_inc(v_cancelTk_x3f_1947_);
lean_inc(v_snap_x3f_1946_);
lean_inc(v_currMacroScope_1945_);
lean_inc(v_quotContext_x3f_1944_);
lean_inc(v_macroStack_1943_);
lean_inc(v_cmdPos_1942_);
lean_inc(v_currRecDepth_1941_);
lean_inc_ref(v_fileMap_1940_);
lean_inc_ref(v_fileName_1939_);
v___x_1950_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1950_, 0, v_fileName_1939_);
lean_ctor_set(v___x_1950_, 1, v_fileMap_1940_);
lean_ctor_set(v___x_1950_, 2, v_currRecDepth_1941_);
lean_ctor_set(v___x_1950_, 3, v_cmdPos_1942_);
lean_ctor_set(v___x_1950_, 4, v_macroStack_1943_);
lean_ctor_set(v___x_1950_, 5, v_quotContext_x3f_1944_);
lean_ctor_set(v___x_1950_, 6, v_currMacroScope_1945_);
lean_ctor_set(v___x_1950_, 7, v_ref_1949_);
lean_ctor_set(v___x_1950_, 8, v_snap_x3f_1946_);
lean_ctor_set(v___x_1950_, 9, v_cancelTk_x3f_1947_);
lean_ctor_set_uint8(v___x_1950_, sizeof(void*)*10, v_suppressElabErrors_1948_);
v___x_1951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1933_, v___x_1950_, v___y_1935_);
lean_dec_ref(v___x_1950_);
return v___x_1951_;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_msg_1933_);
v_a_1952_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1937_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1937_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_1960_, lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_1960_, v_msg_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_ref_1960_);
return v_res_1965_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_val_1983_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = l_Lean_Syntax_getArg(v_stx_1972_, v___x_1990_);
switch(lean_obj_tag(v___x_1991_))
{
case 2:
{
lean_object* v_val_1992_; 
lean_dec(v_stx_1972_);
v_val_1992_ = lean_ctor_get(v___x_1991_, 1);
lean_inc_ref(v_val_1992_);
lean_dec_ref(v___x_1991_);
v_val_1983_ = v_val_1992_;
goto v___jp_1982_;
}
case 1:
{
lean_object* v_kind_1993_; 
v_kind_1993_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_kind_1993_);
if (lean_obj_tag(v_kind_1993_) == 1)
{
lean_object* v_pre_1994_; 
v_pre_1994_ = lean_ctor_get(v_kind_1993_, 0);
lean_inc(v_pre_1994_);
if (lean_obj_tag(v_pre_1994_) == 1)
{
lean_object* v_pre_1995_; 
v_pre_1995_ = lean_ctor_get(v_pre_1994_, 0);
lean_inc(v_pre_1995_);
if (lean_obj_tag(v_pre_1995_) == 1)
{
lean_object* v_pre_1996_; 
v_pre_1996_ = lean_ctor_get(v_pre_1995_, 0);
lean_inc(v_pre_1996_);
if (lean_obj_tag(v_pre_1996_) == 1)
{
lean_object* v_pre_1997_; 
v_pre_1997_ = lean_ctor_get(v_pre_1996_, 0);
if (lean_obj_tag(v_pre_1997_) == 0)
{
lean_object* v_str_1998_; lean_object* v_str_1999_; lean_object* v_str_2000_; lean_object* v_str_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_str_1998_ = lean_ctor_get(v_kind_1993_, 1);
lean_inc_ref(v_str_1998_);
lean_dec_ref(v_kind_1993_);
v_str_1999_ = lean_ctor_get(v_pre_1994_, 1);
lean_inc_ref(v_str_1999_);
lean_dec_ref(v_pre_1994_);
v_str_2000_ = lean_ctor_get(v_pre_1995_, 1);
lean_inc_ref(v_str_2000_);
lean_dec_ref(v_pre_1995_);
v_str_2001_ = lean_ctor_get(v_pre_1996_, 1);
lean_inc_ref(v_str_2001_);
lean_dec_ref(v_pre_1996_);
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0));
v___x_2003_ = lean_string_dec_eq(v_str_2001_, v___x_2002_);
lean_dec_ref(v_str_2001_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v_str_2000_);
lean_dec_ref(v_str_1999_);
lean_dec_ref(v_str_1998_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2005_ = lean_string_dec_eq(v_str_2000_, v___x_2004_);
lean_dec_ref(v_str_2000_);
if (v___x_2005_ == 0)
{
lean_dec_ref(v_str_1999_);
lean_dec_ref(v_str_1998_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
else
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2007_ = lean_string_dec_eq(v_str_1999_, v___x_2006_);
lean_dec_ref(v_str_1999_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v_str_1998_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
else
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2009_ = lean_string_dec_eq(v_str_1998_, v___x_2008_);
lean_dec_ref(v_str_1998_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = l_Lean_Syntax_getArg(v___x_1991_, v___x_2010_);
lean_dec_ref(v___x_1991_);
if (lean_obj_tag(v___x_2011_) == 2)
{
lean_object* v_val_2012_; 
lean_dec(v_stx_1972_);
v_val_2012_ = lean_ctor_get(v___x_2011_, 1);
lean_inc_ref(v_val_2012_);
lean_dec_ref(v___x_2011_);
v_val_1983_ = v_val_2012_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v___x_2011_);
v___x_2013_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1972_);
v___x_2014_ = l_Lean_MessageData_ofSyntax(v_stx_1972_);
v___x_2015_ = l_Lean_indentD(v___x_2014_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2013_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1972_, v___x_2016_, v___y_1973_, v___y_1974_);
lean_dec(v_stx_1972_);
return v___x_2017_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1996_);
lean_dec_ref(v_pre_1995_);
lean_dec_ref(v_pre_1994_);
lean_dec_ref(v_kind_1993_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
}
else
{
lean_dec_ref(v_pre_1995_);
lean_dec(v_pre_1996_);
lean_dec_ref(v_pre_1994_);
lean_dec_ref(v_kind_1993_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
}
else
{
lean_dec(v_pre_1995_);
lean_dec_ref(v_pre_1994_);
lean_dec_ref(v_kind_1993_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
}
else
{
lean_dec(v_pre_1994_);
lean_dec_ref(v_kind_1993_);
lean_dec_ref(v___x_1991_);
goto v___jp_1976_;
}
}
else
{
lean_dec_ref(v___x_1991_);
lean_dec(v_kind_1993_);
goto v___jp_1976_;
}
}
default: 
{
lean_dec(v___x_1991_);
goto v___jp_1976_;
}
}
v___jp_1976_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1977_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1972_);
v___x_1978_ = l_Lean_MessageData_ofSyntax(v_stx_1972_);
v___x_1979_ = l_Lean_indentD(v___x_1978_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1972_, v___x_1980_, v___y_1973_, v___y_1974_);
lean_dec(v_stx_1972_);
return v___x_1981_;
}
v___jp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_string_utf8_byte_size(v_val_1983_);
v___x_1986_ = lean_unsigned_to_nat(2u);
v___x_1987_ = lean_nat_sub(v___x_1985_, v___x_1986_);
v___x_1988_ = lean_string_utf8_extract(v_val_1983_, v___x_1984_, v___x_1987_);
lean_dec(v___x_1987_);
lean_dec_ref(v_val_1983_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2023_, size_t v_sz_2024_, size_t v_i_2025_, lean_object* v_b_2026_){
_start:
{
lean_object* v_a_2028_; uint8_t v___x_2032_; 
v___x_2032_ = lean_usize_dec_lt(v_i_2025_, v_sz_2024_);
if (v___x_2032_ == 0)
{
return v_b_2026_;
}
else
{
lean_object* v_a_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v_out_2036_; uint8_t v___x_2037_; 
v_a_2033_ = lean_array_uget_borrowed(v_as_2023_, v_i_2025_);
v_fst_2034_ = lean_ctor_get(v_a_2033_, 0);
v_snd_2035_ = lean_ctor_get(v_a_2033_, 1);
v_out_2036_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2037_ = lean_string_dec_eq(v_snd_2035_, v_out_2036_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2038_ = lean_unbox(v_fst_2034_);
v___x_2039_ = l_Lean_Diff_Action_linePrefix(v___x_2038_);
v___x_2040_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2041_ = lean_string_append(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_string_append(v___x_2041_, v_snd_2035_);
v___x_2043_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2044_ = lean_string_append(v___x_2042_, v___x_2043_);
v___x_2045_ = lean_string_append(v_b_2026_, v___x_2044_);
lean_dec_ref(v___x_2044_);
v_a_2028_ = v___x_2045_;
goto v___jp_2027_;
}
else
{
uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2046_ = lean_unbox(v_fst_2034_);
v___x_2047_ = l_Lean_Diff_Action_linePrefix(v___x_2046_);
v___x_2048_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2049_ = lean_string_append(v___x_2047_, v___x_2048_);
v___x_2050_ = lean_string_append(v_b_2026_, v___x_2049_);
lean_dec_ref(v___x_2049_);
v_a_2028_ = v___x_2050_;
goto v___jp_2027_;
}
}
v___jp_2027_:
{
size_t v___x_2029_; size_t v___x_2030_; 
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_2025_, v___x_2029_);
v_i_2025_ = v___x_2030_;
v_b_2026_ = v_a_2028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2051_, lean_object* v_sz_2052_, lean_object* v_i_2053_, lean_object* v_b_2054_){
_start:
{
size_t v_sz_boxed_2055_; size_t v_i_boxed_2056_; lean_object* v_res_2057_; 
v_sz_boxed_2055_ = lean_unbox_usize(v_sz_2052_);
lean_dec(v_sz_2052_);
v_i_boxed_2056_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2051_, v_sz_boxed_2055_, v_i_boxed_2056_, v_b_2054_);
lean_dec_ref(v_as_2051_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2058_){
_start:
{
lean_object* v_out_2059_; size_t v_sz_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v_out_2059_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2060_ = lean_array_size(v_lines_2058_);
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2058_, v_sz_2060_, v___x_2061_, v_out_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2063_);
lean_dec_ref(v_lines_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2065_, lean_object* v_as_x27_2066_, lean_object* v_b_2067_){
_start:
{
if (lean_obj_tag(v_as_x27_2066_) == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v_filterFn_2065_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_b_2067_);
return v___x_2069_;
}
else
{
lean_object* v_head_2070_; uint8_t v_isSilent_2071_; 
v_head_2070_ = lean_ctor_get(v_as_x27_2066_, 0);
v_isSilent_2071_ = lean_ctor_get_uint8(v_head_2070_, sizeof(void*)*5 + 2);
if (v_isSilent_2071_ == 0)
{
lean_object* v_tail_2072_; lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2094_; 
lean_inc(v_head_2070_);
v_tail_2072_ = lean_ctor_get(v_as_x27_2066_, 1);
lean_inc(v_tail_2072_);
lean_dec_ref(v_as_x27_2066_);
v_fst_2073_ = lean_ctor_get(v_b_2067_, 0);
v_snd_2074_ = lean_ctor_get(v_b_2067_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_b_2067_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2076_ = v_b_2067_;
v_isShared_2077_ = v_isSharedCheck_2094_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_snd_2074_);
lean_inc(v_fst_2073_);
lean_dec(v_b_2067_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2094_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
lean_inc_ref(v_filterFn_2065_);
lean_inc(v_head_2070_);
v___x_2078_ = lean_apply_1(v_filterFn_2065_, v_head_2070_);
v___x_2079_ = lean_unbox(v___x_2078_);
switch(v___x_2079_)
{
case 0:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = l_Lean_MessageLog_add(v_head_2070_, v_fst_2073_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2080_);
v___x_2082_ = v___x_2076_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_snd_2074_);
v___x_2082_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v_as_x27_2066_ = v_tail_2072_;
v_b_2067_ = v___x_2082_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2086_; 
lean_dec(v_head_2070_);
if (v_isShared_2077_ == 0)
{
v___x_2086_ = v___x_2076_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_fst_2073_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_snd_2074_);
v___x_2086_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v_as_x27_2066_ = v_tail_2072_;
v_b_2067_ = v___x_2086_;
goto _start;
}
}
default: 
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = l_Lean_MessageLog_add(v_head_2070_, v_snd_2074_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2089_);
v___x_2091_ = v___x_2076_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_fst_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
v_as_x27_2066_ = v_tail_2072_;
v_b_2067_ = v___x_2091_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2095_; lean_object* v_fst_2096_; lean_object* v_snd_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_tail_2095_ = lean_ctor_get(v_as_x27_2066_, 1);
lean_inc(v_tail_2095_);
lean_dec_ref(v_as_x27_2066_);
v_fst_2096_ = lean_ctor_get(v_b_2067_, 0);
v_snd_2097_ = lean_ctor_get(v_b_2067_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_b_2067_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v_b_2067_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_snd_2097_);
lean_inc(v_fst_2096_);
lean_dec(v_b_2067_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_fst_2096_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_snd_2097_);
v___x_2102_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
v_as_x27_2066_ = v_tail_2095_;
v_b_2067_ = v___x_2102_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2106_, lean_object* v_as_x27_2107_, lean_object* v_b_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2106_, v_as_x27_2107_, v_b_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2111_, lean_object* v_a_2112_, uint8_t v_b_2113_){
_start:
{
uint8_t v___x_2114_; 
v___x_2114_ = 0;
switch(lean_obj_tag(v_a_2112_))
{
case 0:
{
uint8_t v___x_2115_; 
lean_dec_ref(v_a_2112_);
v___x_2115_ = 1;
return v___x_2115_;
}
case 1:
{
lean_object* v_pos_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2129_; 
v_pos_2116_ = lean_ctor_get(v_a_2112_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_a_2112_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2118_ = v_a_2112_;
v_isShared_2119_ = v_isSharedCheck_2129_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_pos_2116_);
lean_dec(v_a_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2129_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_str_2120_; lean_object* v_startInclusive_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v_str_2120_ = lean_ctor_get(v_s_2111_, 0);
v_startInclusive_2121_ = lean_ctor_get(v_s_2111_, 1);
v___x_2122_ = lean_nat_add(v_startInclusive_2121_, v_pos_2116_);
lean_dec(v_pos_2116_);
v___x_2123_ = lean_string_utf8_next_fast(v_str_2120_, v___x_2122_);
lean_dec(v___x_2122_);
v___x_2124_ = lean_nat_sub(v___x_2123_, v_startInclusive_2121_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2124_);
v___x_2126_ = v___x_2118_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
v_a_2112_ = v___x_2126_;
v_b_2113_ = v___x_2114_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2130_; lean_object* v_table_2131_; lean_object* v_stackPos_2132_; lean_object* v_needlePos_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2186_; 
v_needle_2130_ = lean_ctor_get(v_a_2112_, 0);
v_table_2131_ = lean_ctor_get(v_a_2112_, 1);
v_stackPos_2132_ = lean_ctor_get(v_a_2112_, 2);
v_needlePos_2133_ = lean_ctor_get(v_a_2112_, 3);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_a_2112_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2135_ = v_a_2112_;
v_isShared_2136_ = v_isSharedCheck_2186_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_needlePos_2133_);
lean_inc(v_stackPos_2132_);
lean_inc(v_table_2131_);
lean_inc(v_needle_2130_);
lean_dec(v_a_2112_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2186_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_str_2137_; lean_object* v_startInclusive_2138_; lean_object* v_endExclusive_2139_; lean_object* v_str_2140_; lean_object* v_startInclusive_2141_; lean_object* v_endExclusive_2142_; lean_object* v_basePos_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_str_2137_ = lean_ctor_get(v_needle_2130_, 0);
v_startInclusive_2138_ = lean_ctor_get(v_needle_2130_, 1);
v_endExclusive_2139_ = lean_ctor_get(v_needle_2130_, 2);
v_str_2140_ = lean_ctor_get(v_s_2111_, 0);
v_startInclusive_2141_ = lean_ctor_get(v_s_2111_, 1);
v_endExclusive_2142_ = lean_ctor_get(v_s_2111_, 2);
v_basePos_2143_ = lean_nat_sub(v_stackPos_2132_, v_needlePos_2133_);
v___x_2144_ = lean_nat_sub(v_endExclusive_2139_, v_startInclusive_2138_);
v___x_2145_ = lean_nat_add(v_basePos_2143_, v___x_2144_);
v___x_2146_ = lean_nat_sub(v_endExclusive_2142_, v_startInclusive_2141_);
v___x_2147_ = lean_nat_dec_le(v___x_2145_, v___x_2146_);
lean_dec(v___x_2145_);
if (v___x_2147_ == 0)
{
uint8_t v___x_2148_; 
lean_dec(v___x_2144_);
lean_del_object(v___x_2135_);
lean_dec(v_needlePos_2133_);
lean_dec(v_stackPos_2132_);
lean_dec_ref(v_table_2131_);
lean_dec_ref(v_needle_2130_);
v___x_2148_ = lean_nat_dec_lt(v_basePos_2143_, v___x_2146_);
lean_dec(v___x_2146_);
lean_dec(v_basePos_2143_);
if (v___x_2148_ == 0)
{
return v_b_2113_;
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_box(3);
v_a_2112_ = v___x_2149_;
v_b_2113_ = v___x_2114_;
goto _start;
}
}
else
{
lean_object* v___x_2151_; uint8_t v_stackByte_2152_; lean_object* v___x_2153_; uint8_t v_patByte_2154_; uint8_t v___x_2155_; 
lean_dec(v___x_2146_);
lean_dec(v_basePos_2143_);
v___x_2151_ = lean_nat_add(v_startInclusive_2141_, v_stackPos_2132_);
v_stackByte_2152_ = lean_string_get_byte_fast(v_str_2140_, v___x_2151_);
v___x_2153_ = lean_nat_add(v_startInclusive_2138_, v_needlePos_2133_);
v_patByte_2154_ = lean_string_get_byte_fast(v_str_2137_, v___x_2153_);
v___x_2155_ = lean_uint8_dec_eq(v_stackByte_2152_, v_patByte_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
lean_dec(v___x_2144_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_nat_dec_eq(v_needlePos_2133_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v_newNeedlePos_2160_; uint8_t v___x_2161_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_sub(v_needlePos_2133_, v___x_2158_);
lean_dec(v_needlePos_2133_);
v_newNeedlePos_2160_ = lean_array_fget_borrowed(v_table_2131_, v___x_2159_);
lean_dec(v___x_2159_);
v___x_2161_ = lean_nat_dec_eq(v_newNeedlePos_2160_, v___x_2156_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2163_; 
lean_inc(v_newNeedlePos_2160_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v_newNeedlePos_2160_);
v___x_2163_ = v___x_2135_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_needle_2130_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_table_2131_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_stackPos_2132_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_newNeedlePos_2160_);
v___x_2163_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
v_a_2112_ = v___x_2163_;
v_b_2113_ = v___x_2114_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2166_; lean_object* v___x_2168_; 
v_nextStackPos_2166_ = l_String_Slice_posGE___redArg(v_s_2111_, v_stackPos_2132_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v___x_2156_);
lean_ctor_set(v___x_2135_, 2, v_nextStackPos_2166_);
v___x_2168_ = v___x_2135_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_needle_2130_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_table_2131_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_nextStackPos_2166_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v___x_2156_);
v___x_2168_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_a_2112_ = v___x_2168_;
v_b_2113_ = v___x_2114_;
goto _start;
}
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_nextStackPos_2173_; lean_object* v___x_2175_; 
lean_dec(v_needlePos_2133_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_stackPos_2132_, v___x_2171_);
lean_dec(v_stackPos_2132_);
v_nextStackPos_2173_ = l_String_Slice_posGE___redArg(v_s_2111_, v___x_2172_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v___x_2156_);
lean_ctor_set(v___x_2135_, 2, v_nextStackPos_2173_);
v___x_2175_ = v___x_2135_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_needle_2130_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_table_2131_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_nextStackPos_2173_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v___x_2156_);
v___x_2175_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v_a_2112_ = v___x_2175_;
v_b_2113_ = v___x_2114_;
goto _start;
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v_nextNeedlePos_2179_; uint8_t v___x_2180_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2179_ = lean_nat_add(v_needlePos_2133_, v___x_2178_);
lean_dec(v_needlePos_2133_);
v___x_2180_ = lean_nat_dec_eq(v_nextNeedlePos_2179_, v___x_2144_);
lean_dec(v___x_2144_);
if (v___x_2180_ == 0)
{
lean_object* v_nextStackPos_2181_; lean_object* v___x_2183_; 
v_nextStackPos_2181_ = lean_nat_add(v_stackPos_2132_, v___x_2178_);
lean_dec(v_stackPos_2132_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v_nextNeedlePos_2179_);
lean_ctor_set(v___x_2135_, 2, v_nextStackPos_2181_);
v___x_2183_ = v___x_2135_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_needle_2130_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_table_2131_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_nextStackPos_2181_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_nextNeedlePos_2179_);
v___x_2183_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
v_a_2112_ = v___x_2183_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2179_);
lean_del_object(v___x_2135_);
lean_dec(v_stackPos_2132_);
lean_dec_ref(v_table_2131_);
lean_dec_ref(v_needle_2130_);
return v___x_2180_;
}
}
}
}
}
default: 
{
return v_b_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2187_, lean_object* v_a_2188_, lean_object* v_b_2189_){
_start:
{
uint8_t v_b_boxed_2190_; uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_b_boxed_2190_ = lean_unbox(v_b_2189_);
v_res_2191_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2187_, v_a_2188_, v_b_boxed_2190_);
lean_dec_ref(v_s_2187_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2193_, lean_object* v_s_2194_){
_start:
{
lean_object* v___y_2196_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_string_utf8_byte_size(v___x_2193_);
v___x_2201_ = lean_nat_dec_eq(v___x_2200_, v___x_2199_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2193_);
lean_ctor_set(v___x_2202_, 1, v___x_2199_);
lean_ctor_set(v___x_2202_, 2, v___x_2200_);
v___x_2203_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_ctor_set(v___x_2204_, 2, v___x_2199_);
lean_ctor_set(v___x_2204_, 3, v___x_2199_);
v___y_2196_ = v___x_2204_;
goto v___jp_2195_;
}
else
{
lean_object* v___x_2205_; 
lean_dec_ref(v___x_2193_);
v___x_2205_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2196_ = v___x_2205_;
goto v___jp_2195_;
}
v___jp_2195_:
{
uint8_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = 0;
v___x_2198_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2194_, v___y_2196_, v___x_2197_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2206_, lean_object* v_s_2207_){
_start:
{
uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_res_2208_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2206_, v_s_2207_);
lean_dec_ref(v_s_2207_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2210_, uint8_t v_suppressElabErrors_2211_, lean_object* v_x_2212_){
_start:
{
if (lean_obj_tag(v_x_2212_) == 1)
{
lean_object* v_pre_2213_; 
v_pre_2213_ = lean_ctor_get(v_x_2212_, 0);
if (lean_obj_tag(v_pre_2213_) == 0)
{
lean_object* v_str_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_str_2214_ = lean_ctor_get(v_x_2212_, 1);
v___x_2215_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2216_ = lean_string_dec_eq(v_str_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
return v___y_2210_;
}
else
{
return v_suppressElabErrors_2211_;
}
}
else
{
return v___y_2210_;
}
}
else
{
return v___y_2210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2217_, lean_object* v_suppressElabErrors_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v___y_29318__boxed_2220_; uint8_t v_suppressElabErrors_boxed_2221_; uint8_t v_res_2222_; lean_object* v_r_2223_; 
v___y_29318__boxed_2220_ = lean_unbox(v___y_2217_);
v_suppressElabErrors_boxed_2221_ = lean_unbox(v_suppressElabErrors_2218_);
v_res_2222_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29318__boxed_2220_, v_suppressElabErrors_boxed_2221_, v_x_2219_);
lean_dec(v_x_2219_);
v_r_2223_ = lean_box(v_res_2222_);
return v_r_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2224_, lean_object* v_msgData_2225_, uint8_t v_severity_2226_, uint8_t v_isSilent_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v___y_2232_; uint8_t v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; uint8_t v___y_2295_; uint8_t v___y_2296_; uint8_t v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; uint8_t v___y_2323_; uint8_t v___y_2324_; uint8_t v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; uint8_t v___y_2331_; uint8_t v___y_2332_; uint8_t v___y_2333_; uint8_t v___x_2348_; uint8_t v___y_2350_; uint8_t v___y_2351_; uint8_t v___y_2352_; uint8_t v___y_2354_; uint8_t v___x_2366_; 
v___x_2348_ = 2;
v___x_2366_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2226_, v___x_2348_);
if (v___x_2366_ == 0)
{
v___y_2354_ = v___x_2366_;
goto v___jp_2353_;
}
else
{
uint8_t v___x_2367_; 
lean_inc_ref(v_msgData_2225_);
v___x_2367_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2225_);
v___y_2354_ = v___x_2367_;
goto v___jp_2353_;
}
v___jp_2231_:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Elab_Command_getScope___redArg(v___y_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2242_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2240_);
v___x_2242_ = l_Lean_Elab_Command_getScope___redArg(v___y_2239_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2277_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2277_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2277_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v_currNamespace_2248_; lean_object* v_openDecls_2249_; lean_object* v_env_2250_; lean_object* v_messages_2251_; lean_object* v_scopes_2252_; lean_object* v_usedQuotCtxts_2253_; lean_object* v_nextMacroScope_2254_; lean_object* v_maxRecDepth_2255_; lean_object* v_ngen_2256_; lean_object* v_auxDeclNGen_2257_; lean_object* v_infoState_2258_; lean_object* v_traceState_2259_; lean_object* v_snapshotTasks_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2276_; 
v___x_2247_ = lean_st_ref_take(v___y_2239_);
v_currNamespace_2248_ = lean_ctor_get(v_a_2241_, 2);
lean_inc(v_currNamespace_2248_);
lean_dec(v_a_2241_);
v_openDecls_2249_ = lean_ctor_get(v_a_2243_, 3);
lean_inc(v_openDecls_2249_);
lean_dec(v_a_2243_);
v_env_2250_ = lean_ctor_get(v___x_2247_, 0);
v_messages_2251_ = lean_ctor_get(v___x_2247_, 1);
v_scopes_2252_ = lean_ctor_get(v___x_2247_, 2);
v_usedQuotCtxts_2253_ = lean_ctor_get(v___x_2247_, 3);
v_nextMacroScope_2254_ = lean_ctor_get(v___x_2247_, 4);
v_maxRecDepth_2255_ = lean_ctor_get(v___x_2247_, 5);
v_ngen_2256_ = lean_ctor_get(v___x_2247_, 6);
v_auxDeclNGen_2257_ = lean_ctor_get(v___x_2247_, 7);
v_infoState_2258_ = lean_ctor_get(v___x_2247_, 8);
v_traceState_2259_ = lean_ctor_get(v___x_2247_, 9);
v_snapshotTasks_2260_ = lean_ctor_get(v___x_2247_, 10);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2262_ = v___x_2247_;
v_isShared_2263_ = v_isSharedCheck_2276_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snapshotTasks_2260_);
lean_inc(v_traceState_2259_);
lean_inc(v_infoState_2258_);
lean_inc(v_auxDeclNGen_2257_);
lean_inc(v_ngen_2256_);
lean_inc(v_maxRecDepth_2255_);
lean_inc(v_nextMacroScope_2254_);
lean_inc(v_usedQuotCtxts_2253_);
lean_inc(v_scopes_2252_);
lean_inc(v_messages_2251_);
lean_inc(v_env_2250_);
lean_dec(v___x_2247_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2276_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_currNamespace_2248_);
lean_ctor_set(v___x_2264_, 1, v_openDecls_2249_);
v___x_2265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___y_2234_);
lean_inc_ref(v___y_2237_);
lean_inc_ref(v___y_2236_);
v___x_2266_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2266_, 0, v___y_2236_);
lean_ctor_set(v___x_2266_, 1, v___y_2238_);
lean_ctor_set(v___x_2266_, 2, v___y_2235_);
lean_ctor_set(v___x_2266_, 3, v___y_2237_);
lean_ctor_set(v___x_2266_, 4, v___x_2265_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*5, v___y_2233_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*5 + 1, v___y_2232_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*5 + 2, v_isSilent_2227_);
v___x_2267_ = l_Lean_MessageLog_add(v___x_2266_, v_messages_2251_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 1, v___x_2267_);
v___x_2269_ = v___x_2262_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_env_2250_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_scopes_2252_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_usedQuotCtxts_2253_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v_nextMacroScope_2254_);
lean_ctor_set(v_reuseFailAlloc_2275_, 5, v_maxRecDepth_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 6, v_ngen_2256_);
lean_ctor_set(v_reuseFailAlloc_2275_, 7, v_auxDeclNGen_2257_);
lean_ctor_set(v_reuseFailAlloc_2275_, 8, v_infoState_2258_);
lean_ctor_set(v_reuseFailAlloc_2275_, 9, v_traceState_2259_);
lean_ctor_set(v_reuseFailAlloc_2275_, 10, v_snapshotTasks_2260_);
v___x_2269_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2270_ = lean_st_ref_set(v___y_2239_, v___x_2269_);
v___x_2271_ = lean_box(0);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2271_);
v___x_2273_ = v___x_2245_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2241_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
v_a_2278_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2242_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2242_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
v_a_2286_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2240_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2240_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
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
v___jp_2294_:
{
lean_object* v_fileName_2300_; lean_object* v_fileMap_2301_; uint8_t v_suppressElabErrors_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2321_; 
v_fileName_2300_ = lean_ctor_get(v___y_2228_, 0);
v_fileMap_2301_ = lean_ctor_get(v___y_2228_, 1);
v_suppressElabErrors_2302_ = lean_ctor_get_uint8(v___y_2228_, sizeof(void*)*10);
v___x_2303_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2225_);
v___x_2304_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2303_, v___y_2229_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2321_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2321_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_inc_ref_n(v_fileMap_2301_, 2);
v___x_2309_ = l_Lean_FileMap_toPosition(v_fileMap_2301_, v___y_2298_);
lean_dec(v___y_2298_);
v___x_2310_ = l_Lean_FileMap_toPosition(v_fileMap_2301_, v___y_2299_);
lean_dec(v___y_2299_);
v___x_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2302_ == 0)
{
lean_del_object(v___x_2307_);
v___y_2232_ = v___y_2297_;
v___y_2233_ = v___y_2296_;
v___y_2234_ = v_a_2305_;
v___y_2235_ = v___x_2311_;
v___y_2236_ = v_fileName_2300_;
v___y_2237_ = v___x_2312_;
v___y_2238_ = v___x_2309_;
v___y_2239_ = v___y_2229_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___f_2315_; uint8_t v___x_2316_; 
v___x_2313_ = lean_box(v___y_2295_);
v___x_2314_ = lean_box(v_suppressElabErrors_2302_);
v___f_2315_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2315_, 0, v___x_2313_);
lean_closure_set(v___f_2315_, 1, v___x_2314_);
lean_inc(v_a_2305_);
v___x_2316_ = l_Lean_MessageData_hasTag(v___f_2315_, v_a_2305_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_dec_ref(v___x_2311_);
lean_dec_ref(v___x_2309_);
lean_dec(v_a_2305_);
v___x_2317_ = lean_box(0);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2317_);
v___x_2319_ = v___x_2307_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
else
{
lean_del_object(v___x_2307_);
v___y_2232_ = v___y_2297_;
v___y_2233_ = v___y_2296_;
v___y_2234_ = v_a_2305_;
v___y_2235_ = v___x_2311_;
v___y_2236_ = v_fileName_2300_;
v___y_2237_ = v___x_2312_;
v___y_2238_ = v___x_2309_;
v___y_2239_ = v___y_2229_;
goto v___jp_2231_;
}
}
}
}
v___jp_2322_:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Syntax_getTailPos_x3f(v___y_2326_, v___y_2325_);
lean_dec(v___y_2326_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_inc(v___y_2327_);
v___y_2295_ = v___y_2323_;
v___y_2296_ = v___y_2325_;
v___y_2297_ = v___y_2324_;
v___y_2298_ = v___y_2327_;
v___y_2299_ = v___y_2327_;
goto v___jp_2294_;
}
else
{
lean_object* v_val_2329_; 
v_val_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_val_2329_);
lean_dec_ref(v___x_2328_);
v___y_2295_ = v___y_2323_;
v___y_2296_ = v___y_2325_;
v___y_2297_ = v___y_2324_;
v___y_2298_ = v___y_2327_;
v___y_2299_ = v_val_2329_;
goto v___jp_2294_;
}
}
v___jp_2330_:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Elab_Command_getRef___redArg(v___y_2228_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v_ref_2336_; lean_object* v___x_2337_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2334_);
v_ref_2336_ = l_Lean_replaceRef(v_ref_2224_, v_a_2335_);
lean_dec(v_a_2335_);
v___x_2337_ = l_Lean_Syntax_getPos_x3f(v_ref_2336_, v___y_2332_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_unsigned_to_nat(0u);
v___y_2323_ = v___y_2331_;
v___y_2324_ = v___y_2333_;
v___y_2325_ = v___y_2332_;
v___y_2326_ = v_ref_2336_;
v___y_2327_ = v___x_2338_;
goto v___jp_2322_;
}
else
{
lean_object* v_val_2339_; 
v_val_2339_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_val_2339_);
lean_dec_ref(v___x_2337_);
v___y_2323_ = v___y_2331_;
v___y_2324_ = v___y_2333_;
v___y_2325_ = v___y_2332_;
v___y_2326_ = v_ref_2336_;
v___y_2327_ = v_val_2339_;
goto v___jp_2322_;
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_msgData_2225_);
v_a_2340_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2334_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2334_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
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
v___jp_2349_:
{
if (v___y_2352_ == 0)
{
v___y_2331_ = v___y_2350_;
v___y_2332_ = v___y_2351_;
v___y_2333_ = v_severity_2226_;
goto v___jp_2330_;
}
else
{
v___y_2331_ = v___y_2350_;
v___y_2332_ = v___y_2351_;
v___y_2333_ = v___x_2348_;
goto v___jp_2330_;
}
}
v___jp_2353_:
{
if (v___y_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v_scopes_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_opts_2359_; uint8_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2355_ = lean_st_ref_get(v___y_2229_);
v_scopes_2356_ = lean_ctor_get(v___x_2355_, 2);
lean_inc(v_scopes_2356_);
lean_dec(v___x_2355_);
v___x_2357_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2358_ = l_List_head_x21___redArg(v___x_2357_, v_scopes_2356_);
lean_dec(v_scopes_2356_);
v_opts_2359_ = lean_ctor_get(v___x_2358_, 1);
lean_inc_ref(v_opts_2359_);
lean_dec(v___x_2358_);
v___x_2360_ = 1;
v___x_2361_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2226_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_dec_ref(v_opts_2359_);
v___y_2350_ = v___y_2354_;
v___y_2351_ = v___y_2354_;
v___y_2352_ = v___x_2361_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = l_Lean_warningAsError;
v___x_2363_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2359_, v___x_2362_);
lean_dec_ref(v_opts_2359_);
v___y_2350_ = v___y_2354_;
v___y_2351_ = v___y_2354_;
v___y_2352_ = v___x_2363_;
goto v___jp_2349_;
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec_ref(v_msgData_2225_);
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2368_, lean_object* v_msgData_2369_, lean_object* v_severity_2370_, lean_object* v_isSilent_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
uint8_t v_severity_boxed_2375_; uint8_t v_isSilent_boxed_2376_; lean_object* v_res_2377_; 
v_severity_boxed_2375_ = lean_unbox(v_severity_2370_);
v_isSilent_boxed_2376_ = lean_unbox(v_isSilent_2371_);
v_res_2377_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2368_, v_msgData_2369_, v_severity_boxed_2375_, v_isSilent_boxed_2376_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v_ref_2368_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2378_, lean_object* v_msgData_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v___x_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = 2;
v___x_2384_ = 0;
v___x_2385_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2378_, v_msgData_2379_, v___x_2383_, v___x_2384_, v___y_2380_, v___y_2381_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2386_, lean_object* v_msgData_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2386_, v_msgData_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v_ref_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2392_, lean_object* v___x_2393_, lean_object* v___x_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_){
_start:
{
lean_object* v_it_2398_; lean_object* v_startInclusive_2399_; lean_object* v_endExclusive_2400_; 
if (lean_obj_tag(v_a_2395_) == 0)
{
lean_object* v_currPos_2405_; lean_object* v_searcher_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2435_; 
v_currPos_2405_ = lean_ctor_get(v_a_2395_, 0);
v_searcher_2406_ = lean_ctor_get(v_a_2395_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2395_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2408_ = v_a_2395_;
v_isShared_2409_ = v_isSharedCheck_2435_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_searcher_2406_);
lean_inc(v_currPos_2405_);
lean_dec(v_a_2395_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2435_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_str_2410_; lean_object* v_startInclusive_2411_; lean_object* v_endExclusive_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_str_2410_ = lean_ctor_get(v___x_2393_, 0);
v_startInclusive_2411_ = lean_ctor_get(v___x_2393_, 1);
v_endExclusive_2412_ = lean_ctor_get(v___x_2393_, 2);
v___x_2413_ = lean_nat_sub(v_endExclusive_2412_, v_startInclusive_2411_);
v___x_2414_ = lean_nat_dec_eq(v_searcher_2406_, v___x_2413_);
lean_dec(v___x_2413_);
if (v___x_2414_ == 0)
{
uint32_t v___x_2415_; lean_object* v___x_2416_; uint32_t v___x_2417_; uint8_t v___x_2418_; 
v___x_2415_ = 10;
v___x_2416_ = lean_nat_add(v_startInclusive_2411_, v_searcher_2406_);
v___x_2417_ = lean_string_utf8_get_fast(v_str_2410_, v___x_2416_);
v___x_2418_ = lean_uint32_dec_eq(v___x_2417_, v___x_2415_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
lean_dec(v_searcher_2406_);
v___x_2419_ = lean_string_utf8_next_fast(v_str_2410_, v___x_2416_);
lean_dec(v___x_2416_);
v___x_2420_ = lean_nat_sub(v___x_2419_, v_startInclusive_2411_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___x_2420_);
v___x_2422_ = v___x_2408_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_currPos_2405_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
v_a_2395_ = v___x_2422_;
goto _start;
}
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_slice_2428_; lean_object* v_nextIt_2430_; 
v___x_2425_ = lean_string_utf8_next_fast(v_str_2410_, v___x_2416_);
v___x_2426_ = lean_nat_sub(v___x_2425_, v___x_2416_);
lean_dec(v___x_2416_);
v___x_2427_ = lean_nat_add(v_searcher_2406_, v___x_2426_);
lean_dec(v___x_2426_);
v_slice_2428_ = l_String_Slice_subslice_x21(v___x_2393_, v_currPos_2405_, v_searcher_2406_);
lean_inc(v___x_2427_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___x_2427_);
lean_ctor_set(v___x_2408_, 0, v___x_2427_);
v_nextIt_2430_ = v___x_2408_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2427_);
v_nextIt_2430_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v_startInclusive_2431_; lean_object* v_endExclusive_2432_; 
v_startInclusive_2431_ = lean_ctor_get(v_slice_2428_, 0);
lean_inc(v_startInclusive_2431_);
v_endExclusive_2432_ = lean_ctor_get(v_slice_2428_, 1);
lean_inc(v_endExclusive_2432_);
lean_dec_ref(v_slice_2428_);
v_it_2398_ = v_nextIt_2430_;
v_startInclusive_2399_ = v_startInclusive_2431_;
v_endExclusive_2400_ = v_endExclusive_2432_;
goto v___jp_2397_;
}
}
}
else
{
lean_object* v___x_2434_; 
lean_del_object(v___x_2408_);
lean_dec(v_searcher_2406_);
v___x_2434_ = lean_box(1);
lean_inc(v___x_2394_);
v_it_2398_ = v___x_2434_;
v_startInclusive_2399_ = v_currPos_2405_;
v_endExclusive_2400_ = v___x_2394_;
goto v___jp_2397_;
}
}
}
else
{
lean_dec(v___x_2394_);
lean_dec_ref(v___x_2392_);
return v_b_2396_;
}
v___jp_2397_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_inc_ref(v___x_2392_);
v___x_2401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2392_);
lean_ctor_set(v___x_2401_, 1, v_startInclusive_2399_);
lean_ctor_set(v___x_2401_, 2, v_endExclusive_2400_);
v___x_2402_ = l_String_Slice_toString(v___x_2401_);
lean_dec_ref(v___x_2401_);
v___x_2403_ = lean_array_push(v_b_2396_, v___x_2402_);
v_a_2395_ = v_it_2398_;
v_b_2396_ = v___x_2403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2436_, lean_object* v___x_2437_, lean_object* v___x_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2436_, v___x_2437_, v___x_2438_, v_a_2439_, v_b_2440_);
lean_dec_ref(v___x_2437_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2442_, lean_object* v___x_2443_, lean_object* v___x_2444_, lean_object* v_a_2445_, lean_object* v_b_2446_){
_start:
{
lean_object* v_it_2448_; lean_object* v_startInclusive_2449_; lean_object* v_endExclusive_2450_; 
if (lean_obj_tag(v_a_2445_) == 0)
{
lean_object* v_currPos_2455_; lean_object* v_searcher_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2485_; 
v_currPos_2455_ = lean_ctor_get(v_a_2445_, 0);
v_searcher_2456_ = lean_ctor_get(v_a_2445_, 1);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_a_2445_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2458_ = v_a_2445_;
v_isShared_2459_ = v_isSharedCheck_2485_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_searcher_2456_);
lean_inc(v_currPos_2455_);
lean_dec(v_a_2445_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2485_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_str_2460_; lean_object* v_startInclusive_2461_; lean_object* v_endExclusive_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_str_2460_ = lean_ctor_get(v___x_2443_, 0);
v_startInclusive_2461_ = lean_ctor_get(v___x_2443_, 1);
v_endExclusive_2462_ = lean_ctor_get(v___x_2443_, 2);
v___x_2463_ = lean_nat_sub(v_endExclusive_2462_, v_startInclusive_2461_);
v___x_2464_ = lean_nat_dec_eq(v_searcher_2456_, v___x_2463_);
lean_dec(v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint32_t v___x_2466_; uint32_t v___x_2467_; uint8_t v___x_2468_; 
v___x_2465_ = lean_nat_add(v_startInclusive_2461_, v_searcher_2456_);
v___x_2466_ = lean_string_utf8_get_fast(v_str_2460_, v___x_2465_);
v___x_2467_ = 10;
v___x_2468_ = lean_uint32_dec_eq(v___x_2466_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec(v_searcher_2456_);
v___x_2469_ = lean_string_utf8_next_fast(v_str_2460_, v___x_2465_);
lean_dec(v___x_2465_);
v___x_2470_ = lean_nat_sub(v___x_2469_, v_startInclusive_2461_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2470_);
v___x_2472_ = v___x_2458_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_currPos_2455_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; 
v___x_2473_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2442_, v___x_2443_, v___x_2444_, v___x_2472_, v_b_2446_);
return v___x_2473_;
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_slice_2478_; lean_object* v_nextIt_2480_; 
v___x_2475_ = lean_string_utf8_next_fast(v_str_2460_, v___x_2465_);
v___x_2476_ = lean_nat_sub(v___x_2475_, v___x_2465_);
lean_dec(v___x_2465_);
v___x_2477_ = lean_nat_add(v_searcher_2456_, v___x_2476_);
lean_dec(v___x_2476_);
v_slice_2478_ = l_String_Slice_subslice_x21(v___x_2443_, v_currPos_2455_, v_searcher_2456_);
lean_inc(v___x_2477_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2477_);
lean_ctor_set(v___x_2458_, 0, v___x_2477_);
v_nextIt_2480_ = v___x_2458_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2477_);
v_nextIt_2480_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v_startInclusive_2481_; lean_object* v_endExclusive_2482_; 
v_startInclusive_2481_ = lean_ctor_get(v_slice_2478_, 0);
lean_inc(v_startInclusive_2481_);
v_endExclusive_2482_ = lean_ctor_get(v_slice_2478_, 1);
lean_inc(v_endExclusive_2482_);
lean_dec_ref(v_slice_2478_);
v_it_2448_ = v_nextIt_2480_;
v_startInclusive_2449_ = v_startInclusive_2481_;
v_endExclusive_2450_ = v_endExclusive_2482_;
goto v___jp_2447_;
}
}
}
else
{
lean_object* v___x_2484_; 
lean_del_object(v___x_2458_);
lean_dec(v_searcher_2456_);
v___x_2484_ = lean_box(1);
lean_inc(v___x_2444_);
v_it_2448_ = v___x_2484_;
v_startInclusive_2449_ = v_currPos_2455_;
v_endExclusive_2450_ = v___x_2444_;
goto v___jp_2447_;
}
}
}
else
{
lean_dec(v___x_2444_);
lean_dec_ref(v___x_2442_);
return v_b_2446_;
}
v___jp_2447_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_inc_ref(v___x_2442_);
v___x_2451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2442_);
lean_ctor_set(v___x_2451_, 1, v_startInclusive_2449_);
lean_ctor_set(v___x_2451_, 2, v_endExclusive_2450_);
v___x_2452_ = l_String_Slice_toString(v___x_2451_);
lean_dec_ref(v___x_2451_);
v___x_2453_ = lean_array_push(v_b_2446_, v___x_2452_);
v___x_2454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2442_, v___x_2443_, v___x_2444_, v_it_2448_, v___x_2453_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2486_, lean_object* v___x_2487_, lean_object* v___x_2488_, lean_object* v_a_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2486_, v___x_2487_, v___x_2488_, v_a_2489_, v_b_2490_);
lean_dec_ref(v___x_2487_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v_infoState_2496_; uint8_t v_enabled_2497_; 
v___x_2495_ = lean_st_ref_get(v___y_2493_);
v_infoState_2496_ = lean_ctor_get(v___x_2495_, 8);
lean_inc_ref(v_infoState_2496_);
lean_dec(v___x_2495_);
v_enabled_2497_ = lean_ctor_get_uint8(v_infoState_2496_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2496_);
if (v_enabled_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v_t_2492_);
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; lean_object* v_infoState_2501_; lean_object* v_env_2502_; lean_object* v_messages_2503_; lean_object* v_scopes_2504_; lean_object* v_usedQuotCtxts_2505_; lean_object* v_nextMacroScope_2506_; lean_object* v_maxRecDepth_2507_; lean_object* v_ngen_2508_; lean_object* v_auxDeclNGen_2509_; lean_object* v_traceState_2510_; lean_object* v_snapshotTasks_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2533_; 
v___x_2500_ = lean_st_ref_take(v___y_2493_);
v_infoState_2501_ = lean_ctor_get(v___x_2500_, 8);
v_env_2502_ = lean_ctor_get(v___x_2500_, 0);
v_messages_2503_ = lean_ctor_get(v___x_2500_, 1);
v_scopes_2504_ = lean_ctor_get(v___x_2500_, 2);
v_usedQuotCtxts_2505_ = lean_ctor_get(v___x_2500_, 3);
v_nextMacroScope_2506_ = lean_ctor_get(v___x_2500_, 4);
v_maxRecDepth_2507_ = lean_ctor_get(v___x_2500_, 5);
v_ngen_2508_ = lean_ctor_get(v___x_2500_, 6);
v_auxDeclNGen_2509_ = lean_ctor_get(v___x_2500_, 7);
v_traceState_2510_ = lean_ctor_get(v___x_2500_, 9);
v_snapshotTasks_2511_ = lean_ctor_get(v___x_2500_, 10);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2513_ = v___x_2500_;
v_isShared_2514_ = v_isSharedCheck_2533_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snapshotTasks_2511_);
lean_inc(v_traceState_2510_);
lean_inc(v_infoState_2501_);
lean_inc(v_auxDeclNGen_2509_);
lean_inc(v_ngen_2508_);
lean_inc(v_maxRecDepth_2507_);
lean_inc(v_nextMacroScope_2506_);
lean_inc(v_usedQuotCtxts_2505_);
lean_inc(v_scopes_2504_);
lean_inc(v_messages_2503_);
lean_inc(v_env_2502_);
lean_dec(v___x_2500_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2533_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
uint8_t v_enabled_2515_; lean_object* v_assignment_2516_; lean_object* v_lazyAssignment_2517_; lean_object* v_trees_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2532_; 
v_enabled_2515_ = lean_ctor_get_uint8(v_infoState_2501_, sizeof(void*)*3);
v_assignment_2516_ = lean_ctor_get(v_infoState_2501_, 0);
v_lazyAssignment_2517_ = lean_ctor_get(v_infoState_2501_, 1);
v_trees_2518_ = lean_ctor_get(v_infoState_2501_, 2);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_infoState_2501_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2520_ = v_infoState_2501_;
v_isShared_2521_ = v_isSharedCheck_2532_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_trees_2518_);
lean_inc(v_lazyAssignment_2517_);
lean_inc(v_assignment_2516_);
lean_dec(v_infoState_2501_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2532_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = l_Lean_PersistentArray_push___redArg(v_trees_2518_, v_t_2492_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 2, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_assignment_2516_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_lazyAssignment_2517_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v___x_2522_);
lean_ctor_set_uint8(v_reuseFailAlloc_2531_, sizeof(void*)*3, v_enabled_2515_);
v___x_2524_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 8, v___x_2524_);
v___x_2526_ = v___x_2513_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_env_2502_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_messages_2503_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_scopes_2504_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_usedQuotCtxts_2505_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_nextMacroScope_2506_);
lean_ctor_set(v_reuseFailAlloc_2530_, 5, v_maxRecDepth_2507_);
lean_ctor_set(v_reuseFailAlloc_2530_, 6, v_ngen_2508_);
lean_ctor_set(v_reuseFailAlloc_2530_, 7, v_auxDeclNGen_2509_);
lean_ctor_set(v_reuseFailAlloc_2530_, 8, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2530_, 9, v_traceState_2510_);
lean_ctor_set(v_reuseFailAlloc_2530_, 10, v_snapshotTasks_2511_);
v___x_2526_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = lean_st_ref_set(v___y_2493_, v___x_2526_);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2534_, v___y_2535_);
lean_dec(v___y_2535_);
return v_res_2537_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_unsigned_to_nat(32u);
v___x_2539_ = lean_mk_empty_array_with_capacity(v___x_2538_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2541_ = ((size_t)5ULL);
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_unsigned_to_nat(32u);
v___x_2544_ = lean_mk_empty_array_with_capacity(v___x_2543_);
v___x_2545_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2546_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2544_);
lean_ctor_set(v___x_2546_, 2, v___x_2542_);
lean_ctor_set(v___x_2546_, 3, v___x_2542_);
lean_ctor_set_usize(v___x_2546_, 4, v___x_2541_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v___x_2551_; lean_object* v_infoState_2552_; uint8_t v_enabled_2553_; 
v___x_2551_ = lean_st_ref_get(v___y_2549_);
v_infoState_2552_ = lean_ctor_get(v___x_2551_, 8);
lean_inc_ref(v_infoState_2552_);
lean_dec(v___x_2551_);
v_enabled_2553_ = lean_ctor_get_uint8(v_infoState_2552_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2552_);
if (v_enabled_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec_ref(v_t_2547_);
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_t_2547_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2557_, v___y_2549_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_2564_, lean_object* v_edited_2565_, lean_object* v_b_2566_){
_start:
{
lean_object* v_fst_2567_; lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2587_; 
v_fst_2567_ = lean_ctor_get(v_b_2566_, 0);
v_snd_2568_ = lean_ctor_get(v_b_2566_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_b_2566_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2570_ = v_b_2566_;
v_isShared_2571_ = v_isSharedCheck_2587_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_inc(v_fst_2567_);
lean_dec(v_b_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2587_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_lt(v_snd_2568_, v___x_2564_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2574_; 
if (v_isShared_2571_ == 0)
{
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fst_2567_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_snd_2568_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2576_ = 0;
v___x_2577_ = lean_array_fget_borrowed(v_edited_2565_, v_snd_2568_);
v___x_2578_ = lean_box(v___x_2576_);
lean_inc(v___x_2577_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2577_);
lean_ctor_set(v___x_2570_, 0, v___x_2578_);
v___x_2580_ = v___x_2570_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2577_);
v___x_2580_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = lean_array_push(v_fst_2567_, v___x_2580_);
v___x_2582_ = lean_unsigned_to_nat(1u);
v___x_2583_ = lean_nat_add(v_snd_2568_, v___x_2582_);
lean_dec(v_snd_2568_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2581_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v_b_2566_ = v___x_2584_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_2588_, lean_object* v_edited_2589_, lean_object* v_b_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_2588_, v_edited_2589_, v_b_2590_);
lean_dec_ref(v_edited_2589_);
lean_dec(v___x_2588_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_2592_, lean_object* v___x_2593_, lean_object* v_a_2594_, lean_object* v_b_2595_){
_start:
{
lean_object* v_fst_2596_; lean_object* v_snd_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2622_; 
v_fst_2596_ = lean_ctor_get(v_b_2595_, 0);
v_snd_2597_ = lean_ctor_get(v_b_2595_, 1);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_b_2595_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2599_ = v_b_2595_;
v_isShared_2600_ = v_isSharedCheck_2622_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_snd_2597_);
lean_inc(v_fst_2596_);
lean_dec(v_b_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2622_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; uint8_t v___y_2603_; uint8_t v___x_2618_; 
v___x_2601_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2618_ = lean_nat_dec_lt(v_snd_2597_, v___x_2593_);
if (v___x_2618_ == 0)
{
v___y_2603_ = v___x_2618_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2619_ = lean_array_get_borrowed(v___x_2601_, v_edited_2592_, v_snd_2597_);
v___x_2620_ = lean_string_dec_eq(v___x_2619_, v_a_2594_);
if (v___x_2620_ == 0)
{
v___y_2603_ = v___x_2618_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2621_; 
lean_del_object(v___x_2599_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_fst_2596_);
lean_ctor_set(v___x_2621_, 1, v_snd_2597_);
return v___x_2621_;
}
}
v___jp_2602_:
{
if (v___y_2603_ == 0)
{
lean_object* v___x_2605_; 
if (v_isShared_2600_ == 0)
{
v___x_2605_ = v___x_2599_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_fst_2596_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_snd_2597_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
else
{
uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2607_ = 0;
v___x_2608_ = lean_array_get_borrowed(v___x_2601_, v_edited_2592_, v_snd_2597_);
v___x_2609_ = lean_box(v___x_2607_);
lean_inc(v___x_2608_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 1, v___x_2608_);
lean_ctor_set(v___x_2599_, 0, v___x_2609_);
v___x_2611_ = v___x_2599_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2608_);
v___x_2611_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2612_ = lean_array_push(v_fst_2596_, v___x_2611_);
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_add(v_snd_2597_, v___x_2613_);
lean_dec(v_snd_2597_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2612_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v_b_2595_ = v___x_2615_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_2623_, lean_object* v___x_2624_, lean_object* v_a_2625_, lean_object* v_b_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_2623_, v___x_2624_, v_a_2625_, v_b_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v___x_2624_);
lean_dec_ref(v_edited_2623_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_2628_, lean_object* v___x_2629_, lean_object* v_a_2630_, lean_object* v_b_2631_){
_start:
{
lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2658_; 
v_fst_2632_ = lean_ctor_get(v_b_2631_, 0);
v_snd_2633_ = lean_ctor_get(v_b_2631_, 1);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_b_2631_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2635_ = v_b_2631_;
v_isShared_2636_ = v_isSharedCheck_2658_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_snd_2633_);
lean_inc(v_fst_2632_);
lean_dec(v_b_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2658_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; uint8_t v___y_2639_; uint8_t v___x_2654_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2654_ = lean_nat_dec_lt(v_snd_2633_, v___x_2629_);
if (v___x_2654_ == 0)
{
v___y_2639_ = v___x_2654_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = lean_array_get_borrowed(v___x_2637_, v_original_2628_, v_snd_2633_);
v___x_2656_ = lean_string_dec_eq(v___x_2655_, v_a_2630_);
if (v___x_2656_ == 0)
{
v___y_2639_ = v___x_2654_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2657_; 
lean_del_object(v___x_2635_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_fst_2632_);
lean_ctor_set(v___x_2657_, 1, v_snd_2633_);
return v___x_2657_;
}
}
v___jp_2638_:
{
if (v___y_2639_ == 0)
{
lean_object* v___x_2641_; 
if (v_isShared_2636_ == 0)
{
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_fst_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_snd_2633_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
else
{
uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2643_ = 1;
v___x_2644_ = lean_array_get_borrowed(v___x_2637_, v_original_2628_, v_snd_2633_);
v___x_2645_ = lean_box(v___x_2643_);
lean_inc(v___x_2644_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2644_);
lean_ctor_set(v___x_2635_, 0, v___x_2645_);
v___x_2647_ = v___x_2635_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2644_);
v___x_2647_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = lean_array_push(v_fst_2632_, v___x_2647_);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_snd_2633_, v___x_2649_);
lean_dec(v_snd_2633_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2648_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v_b_2631_ = v___x_2651_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_2659_, lean_object* v___x_2660_, lean_object* v_a_2661_, lean_object* v_b_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_2659_, v___x_2660_, v_a_2661_, v_b_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v___x_2660_);
lean_dec_ref(v_original_2659_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_original_2664_, lean_object* v___x_2665_, lean_object* v_edited_2666_, lean_object* v___x_2667_, lean_object* v_as_2668_, size_t v_sz_2669_, size_t v_i_2670_, lean_object* v_b_2671_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
if (v___x_2672_ == 0)
{
return v_b_2671_;
}
else
{
lean_object* v_snd_2673_; lean_object* v_fst_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2721_; 
v_snd_2673_ = lean_ctor_get(v_b_2671_, 1);
v_fst_2674_ = lean_ctor_get(v_b_2671_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_b_2671_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2676_ = v_b_2671_;
v_isShared_2677_ = v_isSharedCheck_2721_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_snd_2673_);
lean_inc(v_fst_2674_);
lean_dec(v_b_2671_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2721_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2720_; 
v_fst_2678_ = lean_ctor_get(v_snd_2673_, 0);
v_snd_2679_ = lean_ctor_get(v_snd_2673_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_snd_2673_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2681_ = v_snd_2673_;
v_isShared_2682_ = v_isSharedCheck_2720_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_snd_2679_);
lean_inc(v_fst_2678_);
lean_dec(v_snd_2673_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2720_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_a_2683_; lean_object* v___x_2685_; 
v_a_2683_ = lean_array_uget_borrowed(v_as_2668_, v_i_2670_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v_fst_2678_);
lean_ctor_set(v___x_2681_, 0, v_fst_2674_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_fst_2674_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_fst_2678_);
v___x_2685_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v_fst_2687_; lean_object* v_snd_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2718_; 
v___x_2686_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_2664_, v___x_2665_, v_a_2683_, v___x_2685_);
v_fst_2687_ = lean_ctor_get(v___x_2686_, 0);
v_snd_2688_ = lean_ctor_get(v___x_2686_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2690_ = v___x_2686_;
v_isShared_2691_ = v_isSharedCheck_2718_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_snd_2688_);
lean_inc(v_fst_2687_);
lean_dec(v___x_2686_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2718_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 1, v_snd_2679_);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_fst_2687_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_snd_2679_);
v___x_2693_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v_fst_2695_; lean_object* v_snd_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2716_; 
v___x_2694_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_2666_, v___x_2667_, v_a_2683_, v___x_2693_);
v_fst_2695_ = lean_ctor_get(v___x_2694_, 0);
v_snd_2696_ = lean_ctor_get(v___x_2694_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2698_ = v___x_2694_;
v_isShared_2699_ = v_isSharedCheck_2716_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_snd_2696_);
lean_inc(v_fst_2695_);
lean_dec(v___x_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2716_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
uint8_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2700_ = 2;
v___x_2701_ = lean_box(v___x_2700_);
lean_inc(v_a_2683_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v_a_2683_);
lean_ctor_set(v___x_2698_, 0, v___x_2701_);
v___x_2703_ = v___x_2698_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_a_2683_);
v___x_2703_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2704_ = lean_array_push(v_fst_2695_, v___x_2703_);
v___x_2705_ = lean_unsigned_to_nat(1u);
v___x_2706_ = lean_nat_add(v_snd_2688_, v___x_2705_);
lean_dec(v_snd_2688_);
v___x_2707_ = lean_nat_add(v_snd_2696_, v___x_2705_);
lean_dec(v_snd_2696_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v___x_2707_);
lean_ctor_set(v___x_2676_, 0, v___x_2706_);
v___x_2709_ = v___x_2676_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; 
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2704_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = ((size_t)1ULL);
v___x_2712_ = lean_usize_add(v_i_2670_, v___x_2711_);
v_i_2670_ = v___x_2712_;
v_b_2671_ = v___x_2710_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_original_2722_, lean_object* v___x_2723_, lean_object* v_edited_2724_, lean_object* v___x_2725_, lean_object* v_as_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_b_2729_){
_start:
{
size_t v_sz_boxed_2730_; size_t v_i_boxed_2731_; lean_object* v_res_2732_; 
v_sz_boxed_2730_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2731_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2722_, v___x_2723_, v_edited_2724_, v___x_2725_, v_as_2726_, v_sz_boxed_2730_, v_i_boxed_2731_, v_b_2729_);
lean_dec_ref(v_as_2726_);
lean_dec(v___x_2725_);
lean_dec_ref(v_edited_2724_);
lean_dec(v___x_2723_);
lean_dec_ref(v_original_2722_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_2733_, lean_object* v___x_2734_, lean_object* v_original_2735_, lean_object* v___x_2736_, lean_object* v_as_2737_, size_t v_sz_2738_, size_t v_i_2739_, lean_object* v_b_2740_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_lt(v_i_2739_, v_sz_2738_);
if (v___x_2741_ == 0)
{
return v_b_2740_;
}
else
{
lean_object* v_snd_2742_; lean_object* v_fst_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2790_; 
v_snd_2742_ = lean_ctor_get(v_b_2740_, 1);
v_fst_2743_ = lean_ctor_get(v_b_2740_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_b_2740_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2745_ = v_b_2740_;
v_isShared_2746_ = v_isSharedCheck_2790_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snd_2742_);
lean_inc(v_fst_2743_);
lean_dec(v_b_2740_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2790_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_fst_2747_; lean_object* v_snd_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2789_; 
v_fst_2747_ = lean_ctor_get(v_snd_2742_, 0);
v_snd_2748_ = lean_ctor_get(v_snd_2742_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_snd_2742_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2750_ = v_snd_2742_;
v_isShared_2751_ = v_isSharedCheck_2789_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_snd_2748_);
lean_inc(v_fst_2747_);
lean_dec(v_snd_2742_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2789_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_a_2752_; lean_object* v___x_2754_; 
v_a_2752_ = lean_array_uget_borrowed(v_as_2737_, v_i_2739_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 1, v_fst_2747_);
lean_ctor_set(v___x_2750_, 0, v_fst_2743_);
v___x_2754_ = v___x_2750_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_fst_2743_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_fst_2747_);
v___x_2754_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2787_; 
v___x_2755_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_2735_, v___x_2736_, v_a_2752_, v___x_2754_);
v_fst_2756_ = lean_ctor_get(v___x_2755_, 0);
v_snd_2757_ = lean_ctor_get(v___x_2755_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2759_ = v___x_2755_;
v_isShared_2760_ = v_isSharedCheck_2787_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_inc(v_fst_2756_);
lean_dec(v___x_2755_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2787_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v_snd_2748_);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_fst_2756_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_snd_2748_);
v___x_2762_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v_fst_2764_; lean_object* v_snd_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2785_; 
v___x_2763_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_2733_, v___x_2734_, v_a_2752_, v___x_2762_);
v_fst_2764_ = lean_ctor_get(v___x_2763_, 0);
v_snd_2765_ = lean_ctor_get(v___x_2763_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2767_ = v___x_2763_;
v_isShared_2768_ = v_isSharedCheck_2785_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_snd_2765_);
lean_inc(v_fst_2764_);
lean_dec(v___x_2763_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2785_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = 2;
v___x_2770_ = lean_box(v___x_2769_);
lean_inc(v_a_2752_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 1, v_a_2752_);
lean_ctor_set(v___x_2767_, 0, v___x_2770_);
v___x_2772_ = v___x_2767_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_a_2752_);
v___x_2772_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2773_ = lean_array_push(v_fst_2764_, v___x_2772_);
v___x_2774_ = lean_unsigned_to_nat(1u);
v___x_2775_ = lean_nat_add(v_snd_2757_, v___x_2774_);
lean_dec(v_snd_2757_);
v___x_2776_ = lean_nat_add(v_snd_2765_, v___x_2774_);
lean_dec(v_snd_2765_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v___x_2776_);
lean_ctor_set(v___x_2745_, 0, v___x_2775_);
v___x_2778_ = v___x_2745_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; 
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2773_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = ((size_t)1ULL);
v___x_2781_ = lean_usize_add(v_i_2739_, v___x_2780_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2735_, v___x_2736_, v_edited_2733_, v___x_2734_, v_as_2737_, v_sz_2738_, v___x_2781_, v___x_2779_);
return v___x_2782_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_2791_, lean_object* v___x_2792_, lean_object* v_original_2793_, lean_object* v___x_2794_, lean_object* v_as_2795_, lean_object* v_sz_2796_, lean_object* v_i_2797_, lean_object* v_b_2798_){
_start:
{
size_t v_sz_boxed_2799_; size_t v_i_boxed_2800_; lean_object* v_res_2801_; 
v_sz_boxed_2799_ = lean_unbox_usize(v_sz_2796_);
lean_dec(v_sz_2796_);
v_i_boxed_2800_ = lean_unbox_usize(v_i_2797_);
lean_dec(v_i_2797_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_2791_, v___x_2792_, v_original_2793_, v___x_2794_, v_as_2795_, v_sz_boxed_2799_, v_i_boxed_2800_, v_b_2798_);
lean_dec_ref(v_as_2795_);
lean_dec(v___x_2794_);
lean_dec_ref(v_original_2793_);
lean_dec(v___x_2792_);
lean_dec_ref(v_edited_2791_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2802_, lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_box(0);
return v___x_2804_;
}
else
{
lean_object* v_key_2805_; lean_object* v_value_2806_; lean_object* v_tail_2807_; uint8_t v___x_2808_; 
v_key_2805_ = lean_ctor_get(v_x_2803_, 0);
v_value_2806_ = lean_ctor_get(v_x_2803_, 1);
v_tail_2807_ = lean_ctor_get(v_x_2803_, 2);
v___x_2808_ = lean_string_dec_eq(v_key_2805_, v_a_2802_);
if (v___x_2808_ == 0)
{
v_x_2803_ = v_tail_2807_;
goto _start;
}
else
{
lean_object* v___x_2810_; 
lean_inc(v_value_2806_);
v___x_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_value_2806_);
return v___x_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2811_, lean_object* v_x_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2811_, v_x_2812_);
lean_dec(v_x_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_buckets_2816_; lean_object* v___x_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; uint64_t v_fold_2821_; uint64_t v___x_2822_; uint64_t v___x_2823_; uint64_t v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_buckets_2816_ = lean_ctor_get(v_m_2814_, 1);
v___x_2817_ = lean_array_get_size(v_buckets_2816_);
v___x_2818_ = lean_string_hash(v_a_2815_);
v___x_2819_ = 32ULL;
v___x_2820_ = lean_uint64_shift_right(v___x_2818_, v___x_2819_);
v_fold_2821_ = lean_uint64_xor(v___x_2818_, v___x_2820_);
v___x_2822_ = 16ULL;
v___x_2823_ = lean_uint64_shift_right(v_fold_2821_, v___x_2822_);
v___x_2824_ = lean_uint64_xor(v_fold_2821_, v___x_2823_);
v___x_2825_ = lean_uint64_to_usize(v___x_2824_);
v___x_2826_ = lean_usize_of_nat(v___x_2817_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_sub(v___x_2826_, v___x_2827_);
v___x_2829_ = lean_usize_land(v___x_2825_, v___x_2828_);
v___x_2830_ = lean_array_uget_borrowed(v_buckets_2816_, v___x_2829_);
v___x_2831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2815_, v___x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2832_, v_a_2833_);
lean_dec_ref(v_a_2833_);
lean_dec_ref(v_m_2832_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2835_, lean_object* v_b_2836_, lean_object* v_x_2837_){
_start:
{
if (lean_obj_tag(v_x_2837_) == 0)
{
lean_dec(v_b_2836_);
lean_dec_ref(v_a_2835_);
return v_x_2837_;
}
else
{
lean_object* v_key_2838_; lean_object* v_value_2839_; lean_object* v_tail_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2852_; 
v_key_2838_ = lean_ctor_get(v_x_2837_, 0);
v_value_2839_ = lean_ctor_get(v_x_2837_, 1);
v_tail_2840_ = lean_ctor_get(v_x_2837_, 2);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_x_2837_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2842_ = v_x_2837_;
v_isShared_2843_ = v_isSharedCheck_2852_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_tail_2840_);
lean_inc(v_value_2839_);
lean_inc(v_key_2838_);
lean_dec(v_x_2837_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2852_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_string_dec_eq(v_key_2838_, v_a_2835_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2835_, v_b_2836_, v_tail_2840_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 2, v___x_2845_);
v___x_2847_ = v___x_2842_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_key_2838_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_value_2839_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
else
{
lean_object* v___x_2850_; 
lean_dec(v_value_2839_);
lean_dec(v_key_2838_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 1, v_b_2836_);
lean_ctor_set(v___x_2842_, 0, v_a_2835_);
v___x_2850_ = v___x_2842_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2835_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_b_2836_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_tail_2840_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2853_, lean_object* v_x_2854_){
_start:
{
if (lean_obj_tag(v_x_2854_) == 0)
{
uint8_t v___x_2855_; 
v___x_2855_ = 0;
return v___x_2855_;
}
else
{
lean_object* v_key_2856_; lean_object* v_tail_2857_; uint8_t v___x_2858_; 
v_key_2856_ = lean_ctor_get(v_x_2854_, 0);
v_tail_2857_ = lean_ctor_get(v_x_2854_, 2);
v___x_2858_ = lean_string_dec_eq(v_key_2856_, v_a_2853_);
if (v___x_2858_ == 0)
{
v_x_2854_ = v_tail_2857_;
goto _start;
}
else
{
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2860_, lean_object* v_x_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2860_, v_x_2861_);
lean_dec(v_x_2861_);
lean_dec_ref(v_a_2860_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
if (lean_obj_tag(v_x_2865_) == 0)
{
return v_x_2864_;
}
else
{
lean_object* v_key_2866_; lean_object* v_value_2867_; lean_object* v_tail_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2891_; 
v_key_2866_ = lean_ctor_get(v_x_2865_, 0);
v_value_2867_ = lean_ctor_get(v_x_2865_, 1);
v_tail_2868_ = lean_ctor_get(v_x_2865_, 2);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_x_2865_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2870_ = v_x_2865_;
v_isShared_2871_ = v_isSharedCheck_2891_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_tail_2868_);
lean_inc(v_value_2867_);
lean_inc(v_key_2866_);
lean_dec(v_x_2865_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2891_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; uint64_t v___x_2873_; uint64_t v___x_2874_; uint64_t v___x_2875_; uint64_t v_fold_2876_; uint64_t v___x_2877_; uint64_t v___x_2878_; uint64_t v___x_2879_; size_t v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; size_t v___x_2883_; size_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2872_ = lean_array_get_size(v_x_2864_);
v___x_2873_ = lean_string_hash(v_key_2866_);
v___x_2874_ = 32ULL;
v___x_2875_ = lean_uint64_shift_right(v___x_2873_, v___x_2874_);
v_fold_2876_ = lean_uint64_xor(v___x_2873_, v___x_2875_);
v___x_2877_ = 16ULL;
v___x_2878_ = lean_uint64_shift_right(v_fold_2876_, v___x_2877_);
v___x_2879_ = lean_uint64_xor(v_fold_2876_, v___x_2878_);
v___x_2880_ = lean_uint64_to_usize(v___x_2879_);
v___x_2881_ = lean_usize_of_nat(v___x_2872_);
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_sub(v___x_2881_, v___x_2882_);
v___x_2884_ = lean_usize_land(v___x_2880_, v___x_2883_);
v___x_2885_ = lean_array_uget_borrowed(v_x_2864_, v___x_2884_);
lean_inc(v___x_2885_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 2, v___x_2885_);
v___x_2887_ = v___x_2870_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_key_2866_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_value_2867_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_array_uset(v_x_2864_, v___x_2884_, v___x_2887_);
v_x_2864_ = v___x_2888_;
v_x_2865_ = v_tail_2868_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2892_, lean_object* v_source_2893_, lean_object* v_target_2894_){
_start:
{
lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = lean_array_get_size(v_source_2893_);
v___x_2896_ = lean_nat_dec_lt(v_i_2892_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_dec_ref(v_source_2893_);
lean_dec(v_i_2892_);
return v_target_2894_;
}
else
{
lean_object* v_es_2897_; lean_object* v___x_2898_; lean_object* v_source_2899_; lean_object* v_target_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_es_2897_ = lean_array_fget(v_source_2893_, v_i_2892_);
v___x_2898_ = lean_box(0);
v_source_2899_ = lean_array_fset(v_source_2893_, v_i_2892_, v___x_2898_);
v_target_2900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2894_, v_es_2897_);
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = lean_nat_add(v_i_2892_, v___x_2901_);
lean_dec(v_i_2892_);
v_i_2892_ = v___x_2902_;
v_source_2893_ = v_source_2899_;
v_target_2894_ = v_target_2900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2904_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_nbuckets_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2905_ = lean_array_get_size(v_data_2904_);
v___x_2906_ = lean_unsigned_to_nat(2u);
v_nbuckets_2907_ = lean_nat_mul(v___x_2905_, v___x_2906_);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_mk_array(v_nbuckets_2907_, v___x_2909_);
v___x_2911_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2908_, v_data_2904_, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2912_, lean_object* v_a_2913_, lean_object* v_b_2914_){
_start:
{
lean_object* v_size_2915_; lean_object* v_buckets_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2959_; 
v_size_2915_ = lean_ctor_get(v_m_2912_, 0);
v_buckets_2916_ = lean_ctor_get(v_m_2912_, 1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_m_2912_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2918_ = v_m_2912_;
v_isShared_2919_ = v_isSharedCheck_2959_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_buckets_2916_);
lean_inc(v_size_2915_);
lean_dec(v_m_2912_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2959_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v_fold_2924_; uint64_t v___x_2925_; uint64_t v___x_2926_; uint64_t v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; lean_object* v_bkt_2933_; uint8_t v___x_2934_; 
v___x_2920_ = lean_array_get_size(v_buckets_2916_);
v___x_2921_ = lean_string_hash(v_a_2913_);
v___x_2922_ = 32ULL;
v___x_2923_ = lean_uint64_shift_right(v___x_2921_, v___x_2922_);
v_fold_2924_ = lean_uint64_xor(v___x_2921_, v___x_2923_);
v___x_2925_ = 16ULL;
v___x_2926_ = lean_uint64_shift_right(v_fold_2924_, v___x_2925_);
v___x_2927_ = lean_uint64_xor(v_fold_2924_, v___x_2926_);
v___x_2928_ = lean_uint64_to_usize(v___x_2927_);
v___x_2929_ = lean_usize_of_nat(v___x_2920_);
v___x_2930_ = ((size_t)1ULL);
v___x_2931_ = lean_usize_sub(v___x_2929_, v___x_2930_);
v___x_2932_ = lean_usize_land(v___x_2928_, v___x_2931_);
v_bkt_2933_ = lean_array_uget_borrowed(v_buckets_2916_, v___x_2932_);
v___x_2934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2913_, v_bkt_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v_size_x27_2936_; lean_object* v___x_2937_; lean_object* v_buckets_x27_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2935_ = lean_unsigned_to_nat(1u);
v_size_x27_2936_ = lean_nat_add(v_size_2915_, v___x_2935_);
lean_dec(v_size_2915_);
lean_inc(v_bkt_2933_);
v___x_2937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2937_, 0, v_a_2913_);
lean_ctor_set(v___x_2937_, 1, v_b_2914_);
lean_ctor_set(v___x_2937_, 2, v_bkt_2933_);
v_buckets_x27_2938_ = lean_array_uset(v_buckets_2916_, v___x_2932_, v___x_2937_);
v___x_2939_ = lean_unsigned_to_nat(4u);
v___x_2940_ = lean_nat_mul(v_size_x27_2936_, v___x_2939_);
v___x_2941_ = lean_unsigned_to_nat(3u);
v___x_2942_ = lean_nat_div(v___x_2940_, v___x_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_array_get_size(v_buckets_x27_2938_);
v___x_2944_ = lean_nat_dec_le(v___x_2942_, v___x_2943_);
lean_dec(v___x_2942_);
if (v___x_2944_ == 0)
{
lean_object* v_val_2945_; lean_object* v___x_2947_; 
v_val_2945_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_2938_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v_val_2945_);
lean_ctor_set(v___x_2918_, 0, v_size_x27_2936_);
v___x_2947_ = v___x_2918_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_size_x27_2936_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_val_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
else
{
lean_object* v___x_2950_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v_buckets_x27_2938_);
lean_ctor_set(v___x_2918_, 0, v_size_x27_2936_);
v___x_2950_ = v___x_2918_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_size_x27_2936_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_buckets_x27_2938_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
else
{
lean_object* v___x_2952_; lean_object* v_buckets_x27_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_inc(v_bkt_2933_);
v___x_2952_ = lean_box(0);
v_buckets_x27_2953_ = lean_array_uset(v_buckets_2916_, v___x_2932_, v___x_2952_);
v___x_2954_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2913_, v_b_2914_, v_bkt_2933_);
v___x_2955_ = lean_array_uset(v_buckets_x27_2953_, v___x_2932_, v___x_2954_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v___x_2955_);
v___x_2957_ = v___x_2918_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_size_2915_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_2960_, lean_object* v_index_2961_, lean_object* v_val_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_2960_, v_val_2962_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2964_ = lean_unsigned_to_nat(1u);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_index_2961_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2964_);
lean_ctor_set(v___x_2968_, 1, v___x_2965_);
lean_ctor_set(v___x_2968_, 2, v___x_2966_);
lean_ctor_set(v___x_2968_, 3, v___x_2967_);
v___x_2969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2960_, v_val_2962_, v___x_2968_);
return v___x_2969_;
}
else
{
lean_object* v_val_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2991_; 
v_val_2970_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2972_ = v___x_2963_;
v_isShared_2973_ = v_isSharedCheck_2991_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_val_2970_);
lean_dec(v___x_2963_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2991_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_leftCount_2974_; lean_object* v_rightCount_2975_; lean_object* v_rightIndex_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2989_; 
v_leftCount_2974_ = lean_ctor_get(v_val_2970_, 0);
v_rightCount_2975_ = lean_ctor_get(v_val_2970_, 2);
v_rightIndex_2976_ = lean_ctor_get(v_val_2970_, 3);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_val_2970_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_val_2970_, 1);
lean_dec(v_unused_2990_);
v___x_2978_ = v_val_2970_;
v_isShared_2979_ = v_isSharedCheck_2989_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_rightIndex_2976_);
lean_inc(v_rightCount_2975_);
lean_inc(v_leftCount_2974_);
lean_dec(v_val_2970_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2989_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_add(v_leftCount_2974_, v___x_2980_);
lean_dec(v_leftCount_2974_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v_index_2961_);
v___x_2983_ = v___x_2972_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_index_2961_);
v___x_2983_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2985_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v___x_2983_);
lean_ctor_set(v___x_2978_, 0, v___x_2981_);
v___x_2985_ = v___x_2978_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_rightCount_2975_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_rightIndex_2976_);
v___x_2985_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2960_, v_val_2962_, v___x_2985_);
return v___x_2986_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_2992_, lean_object* v_fst_2993_, lean_object* v___x_2994_, lean_object* v_fst_2995_, lean_object* v_a_2996_, lean_object* v_b_2997_){
_start:
{
uint8_t v___x_2998_; 
v___x_2998_ = lean_nat_dec_lt(v_a_2996_, v_upperBound_2992_);
if (v___x_2998_ == 0)
{
lean_dec(v_a_2996_);
return v_b_2997_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = l_Subarray_get___redArg(v_fst_2995_, v_a_2996_);
lean_inc(v_a_2996_);
v___x_3000_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_2997_, v_a_2996_, v___x_2999_);
v___x_3001_ = lean_unsigned_to_nat(1u);
v___x_3002_ = lean_nat_add(v_a_2996_, v___x_3001_);
lean_dec(v_a_2996_);
v_a_2996_ = v___x_3002_;
v_b_2997_ = v___x_3000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3004_, lean_object* v_fst_3005_, lean_object* v___x_3006_, lean_object* v_fst_3007_, lean_object* v_a_3008_, lean_object* v_b_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3004_, v_fst_3005_, v___x_3006_, v_fst_3007_, v_a_3008_, v_b_3009_);
lean_dec_ref(v_fst_3007_);
lean_dec(v___x_3006_);
lean_dec_ref(v_fst_3005_);
lean_dec(v_upperBound_3004_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3011_, lean_object* v_x_3012_){
_start:
{
if (lean_obj_tag(v_x_3012_) == 0)
{
lean_inc(v_x_3011_);
return v_x_3011_;
}
else
{
lean_object* v_key_3013_; lean_object* v_value_3014_; lean_object* v_tail_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_key_3013_ = lean_ctor_get(v_x_3012_, 0);
v_value_3014_ = lean_ctor_get(v_x_3012_, 1);
v_tail_3015_ = lean_ctor_get(v_x_3012_, 2);
v___x_3016_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3011_, v_tail_3015_);
lean_inc(v_value_3014_);
lean_inc(v_key_3013_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_key_3013_);
lean_ctor_set(v___x_3017_, 1, v_value_3014_);
v___x_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3016_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3019_, v_x_3020_);
lean_dec(v_x_3020_);
lean_dec(v_x_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3022_, size_t v_i_3023_, size_t v_stop_3024_, lean_object* v_b_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_eq(v_i_3023_, v_stop_3024_);
if (v___x_3026_ == 0)
{
size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_sub(v_i_3023_, v___x_3027_);
v___x_3029_ = lean_array_uget_borrowed(v_as_3022_, v___x_3028_);
v___x_3030_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3025_, v___x_3029_);
lean_dec(v_b_3025_);
v_i_3023_ = v___x_3028_;
v_b_3025_ = v___x_3030_;
goto _start;
}
else
{
return v_b_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3032_, lean_object* v_i_3033_, lean_object* v_stop_3034_, lean_object* v_b_3035_){
_start:
{
size_t v_i_boxed_3036_; size_t v_stop_boxed_3037_; lean_object* v_res_3038_; 
v_i_boxed_3036_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_stop_boxed_3037_ = lean_unbox_usize(v_stop_3034_);
lean_dec(v_stop_3034_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3032_, v_i_boxed_3036_, v_stop_boxed_3037_, v_b_3035_);
lean_dec_ref(v_as_3032_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3039_, lean_object* v_right_3040_, lean_object* v_pref_3041_){
_start:
{
lean_object* v_start_3042_; lean_object* v_stop_3043_; lean_object* v_i_3044_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v_start_3042_ = lean_ctor_get(v_left_3039_, 1);
v_stop_3043_ = lean_ctor_get(v_left_3039_, 2);
v_i_3044_ = lean_array_get_size(v_pref_3041_);
v___x_3050_ = lean_nat_sub(v_stop_3043_, v_start_3042_);
v___x_3051_ = lean_nat_dec_lt(v_i_3044_, v___x_3050_);
lean_dec(v___x_3050_);
if (v___x_3051_ == 0)
{
goto v___jp_3045_;
}
else
{
lean_object* v_start_3052_; lean_object* v_stop_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_start_3052_ = lean_ctor_get(v_right_3040_, 1);
v_stop_3053_ = lean_ctor_get(v_right_3040_, 2);
v___x_3054_ = lean_nat_sub(v_stop_3053_, v_start_3052_);
v___x_3055_ = lean_nat_dec_lt(v_i_3044_, v___x_3054_);
lean_dec(v___x_3054_);
if (v___x_3055_ == 0)
{
goto v___jp_3045_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3056_ = l_Subarray_get___redArg(v_left_3039_, v_i_3044_);
v___x_3057_ = l_Subarray_get___redArg(v_right_3040_, v_i_3044_);
v___x_3058_ = lean_string_dec_eq(v___x_3056_, v___x_3057_);
lean_dec(v___x_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v___x_3056_);
v___x_3059_ = l_Subarray_drop___redArg(v_left_3039_, v_i_3044_);
v___x_3060_ = l_Subarray_drop___redArg(v_right_3040_, v_i_3044_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v_pref_3041_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
return v___x_3062_;
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_array_push(v_pref_3041_, v___x_3056_);
v_pref_3041_ = v___x_3063_;
goto _start;
}
}
}
v___jp_3045_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = l_Subarray_drop___redArg(v_left_3039_, v_i_3044_);
v___x_3047_ = l_Subarray_drop___redArg(v_right_3040_, v_i_3044_);
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v_pref_3041_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3067_, lean_object* v_right_3068_){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3070_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3067_, v_right_3068_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3071_, lean_object* v_b_3072_){
_start:
{
lean_object* v_array_3073_; lean_object* v_start_3074_; lean_object* v_stop_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3088_; 
v_array_3073_ = lean_ctor_get(v_a_3071_, 0);
v_start_3074_ = lean_ctor_get(v_a_3071_, 1);
v_stop_3075_ = lean_ctor_get(v_a_3071_, 2);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_a_3071_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3077_ = v_a_3071_;
v_isShared_3078_ = v_isSharedCheck_3088_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_stop_3075_);
lean_inc(v_start_3074_);
lean_inc(v_array_3073_);
lean_dec(v_a_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3088_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_nat_dec_lt(v_start_3074_, v_stop_3075_);
if (v___x_3079_ == 0)
{
lean_del_object(v___x_3077_);
lean_dec(v_stop_3075_);
lean_dec(v_start_3074_);
lean_dec_ref(v_array_3073_);
return v_b_3072_;
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3080_ = lean_unsigned_to_nat(1u);
v___x_3081_ = lean_nat_add(v_start_3074_, v___x_3080_);
lean_inc_ref(v_array_3073_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_3081_);
v___x_3083_ = v___x_3077_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_array_3073_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_stop_3075_);
v___x_3083_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_array_fget(v_array_3073_, v_start_3074_);
lean_dec(v_start_3074_);
lean_dec_ref(v_array_3073_);
v___x_3085_ = lean_array_push(v_b_3072_, v___x_3084_);
v_a_3071_ = v___x_3083_;
v_b_3072_ = v___x_3085_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3089_, lean_object* v_right_3090_, lean_object* v_i_3091_){
_start:
{
lean_object* v_start_3092_; lean_object* v_stop_3093_; lean_object* v___x_3094_; uint8_t v___x_3108_; 
v_start_3092_ = lean_ctor_get(v_left_3089_, 1);
v_stop_3093_ = lean_ctor_get(v_left_3089_, 2);
v___x_3094_ = lean_nat_sub(v_stop_3093_, v_start_3092_);
v___x_3108_ = lean_nat_dec_lt(v_i_3091_, v___x_3094_);
if (v___x_3108_ == 0)
{
goto v___jp_3095_;
}
else
{
lean_object* v_start_3109_; lean_object* v_stop_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v_start_3109_ = lean_ctor_get(v_right_3090_, 1);
v_stop_3110_ = lean_ctor_get(v_right_3090_, 2);
v___x_3111_ = lean_nat_sub(v_stop_3110_, v_start_3109_);
v___x_3112_ = lean_nat_dec_lt(v_i_3091_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_dec(v___x_3111_);
goto v___jp_3095_;
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3113_ = lean_nat_sub(v___x_3094_, v_i_3091_);
lean_dec(v___x_3094_);
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3115_ = lean_nat_sub(v___x_3113_, v___x_3114_);
v___x_3116_ = l_Subarray_get___redArg(v_left_3089_, v___x_3115_);
lean_dec(v___x_3115_);
v___x_3117_ = lean_nat_sub(v___x_3111_, v_i_3091_);
lean_dec(v___x_3111_);
v___x_3118_ = lean_nat_sub(v___x_3117_, v___x_3114_);
v___x_3119_ = l_Subarray_get___redArg(v_right_3090_, v___x_3118_);
lean_dec(v___x_3118_);
v___x_3120_ = lean_string_dec_eq(v___x_3116_, v___x_3119_);
lean_dec(v___x_3119_);
lean_dec(v___x_3116_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v_i_3091_);
lean_inc_ref(v_left_3089_);
v___x_3121_ = l_Subarray_take___redArg(v_left_3089_, v___x_3113_);
v___x_3122_ = l_Subarray_take___redArg(v_right_3090_, v___x_3117_);
lean_dec(v___x_3117_);
v___x_3123_ = l_Subarray_drop___redArg(v_left_3089_, v___x_3113_);
lean_dec(v___x_3113_);
v___x_3124_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3125_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3123_, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3122_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3121_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
return v___x_3127_;
}
else
{
lean_object* v___x_3128_; 
lean_dec(v___x_3117_);
lean_dec(v___x_3113_);
v___x_3128_ = lean_nat_add(v_i_3091_, v___x_3114_);
lean_dec(v_i_3091_);
v_i_3091_ = v___x_3128_;
goto _start;
}
}
}
v___jp_3095_:
{
lean_object* v_start_3096_; lean_object* v_stop_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_start_3096_ = lean_ctor_get(v_right_3090_, 1);
v_stop_3097_ = lean_ctor_get(v_right_3090_, 2);
v___x_3098_ = lean_nat_sub(v___x_3094_, v_i_3091_);
lean_dec(v___x_3094_);
lean_inc_ref(v_left_3089_);
v___x_3099_ = l_Subarray_take___redArg(v_left_3089_, v___x_3098_);
v___x_3100_ = lean_nat_sub(v_stop_3097_, v_start_3096_);
v___x_3101_ = lean_nat_sub(v___x_3100_, v_i_3091_);
lean_dec(v_i_3091_);
lean_dec(v___x_3100_);
v___x_3102_ = l_Subarray_take___redArg(v_right_3090_, v___x_3101_);
lean_dec(v___x_3101_);
v___x_3103_ = l_Subarray_drop___redArg(v_left_3089_, v___x_3098_);
lean_dec(v___x_3098_);
v___x_3104_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3105_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3103_, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3102_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3099_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
return v___x_3107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3130_, lean_object* v_right_3131_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3130_, v_right_3131_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3134_, lean_object* v_b_3135_){
_start:
{
if (lean_obj_tag(v_as_x27_3134_) == 0)
{
return v_b_3135_;
}
else
{
lean_object* v_head_3136_; lean_object* v_snd_3137_; lean_object* v_leftIndex_3138_; 
v_head_3136_ = lean_ctor_get(v_as_x27_3134_, 0);
lean_inc(v_head_3136_);
v_snd_3137_ = lean_ctor_get(v_head_3136_, 1);
lean_inc(v_snd_3137_);
v_leftIndex_3138_ = lean_ctor_get(v_snd_3137_, 1);
lean_inc(v_leftIndex_3138_);
if (lean_obj_tag(v_leftIndex_3138_) == 1)
{
lean_object* v_rightIndex_3139_; 
v_rightIndex_3139_ = lean_ctor_get(v_snd_3137_, 3);
lean_inc(v_rightIndex_3139_);
if (lean_obj_tag(v_rightIndex_3139_) == 1)
{
if (lean_obj_tag(v_b_3135_) == 0)
{
lean_object* v_tail_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3170_; 
v_tail_3140_ = lean_ctor_get(v_as_x27_3134_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_as_x27_3134_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v_as_x27_3134_, 0);
lean_dec(v_unused_3171_);
v___x_3142_ = v_as_x27_3134_;
v_isShared_3143_ = v_isSharedCheck_3170_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_tail_3140_);
lean_dec(v_as_x27_3134_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3170_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_fst_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3168_; 
v_fst_3144_ = lean_ctor_get(v_head_3136_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_head_3136_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v_head_3136_, 1);
lean_dec(v_unused_3169_);
v___x_3146_ = v_head_3136_;
v_isShared_3147_ = v_isSharedCheck_3168_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_fst_3144_);
lean_dec(v_head_3136_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3168_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_leftCount_3148_; lean_object* v_rightCount_3149_; lean_object* v_val_3150_; lean_object* v_val_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3167_; 
v_leftCount_3148_ = lean_ctor_get(v_snd_3137_, 0);
lean_inc(v_leftCount_3148_);
v_rightCount_3149_ = lean_ctor_get(v_snd_3137_, 2);
lean_inc(v_rightCount_3149_);
lean_dec(v_snd_3137_);
v_val_3150_ = lean_ctor_get(v_leftIndex_3138_, 0);
lean_inc(v_val_3150_);
lean_dec_ref(v_leftIndex_3138_);
v_val_3151_ = lean_ctor_get(v_rightIndex_3139_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_rightIndex_3139_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3153_ = v_rightIndex_3139_;
v_isShared_3154_ = v_isSharedCheck_3167_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_val_3151_);
lean_dec(v_rightIndex_3139_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3167_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_nat_add(v_leftCount_3148_, v_rightCount_3149_);
lean_dec(v_rightCount_3149_);
lean_dec(v_leftCount_3148_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 1, v_val_3151_);
lean_ctor_set(v___x_3146_, 0, v_val_3150_);
v___x_3157_ = v___x_3146_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_val_3150_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_val_3151_);
v___x_3157_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3159_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 0);
lean_ctor_set(v___x_3142_, 1, v___x_3157_);
lean_ctor_set(v___x_3142_, 0, v_fst_3144_);
v___x_3159_ = v___x_3142_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_fst_3144_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3155_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3160_);
v___x_3162_ = v___x_3153_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
v_as_x27_3134_ = v_tail_3140_;
v_b_3135_ = v___x_3162_;
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
lean_object* v_val_3172_; lean_object* v_tail_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3214_; 
v_val_3172_ = lean_ctor_get(v_b_3135_, 0);
lean_inc(v_val_3172_);
v_tail_3173_ = lean_ctor_get(v_as_x27_3134_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_as_x27_3134_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v_as_x27_3134_, 0);
lean_dec(v_unused_3215_);
v___x_3175_ = v_as_x27_3134_;
v_isShared_3176_ = v_isSharedCheck_3214_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_tail_3173_);
lean_dec(v_as_x27_3134_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3214_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_fst_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3212_; 
v_fst_3177_ = lean_ctor_get(v_head_3136_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_head_3136_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_head_3136_, 1);
lean_dec(v_unused_3213_);
v___x_3179_ = v_head_3136_;
v_isShared_3180_ = v_isSharedCheck_3212_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_fst_3177_);
lean_dec(v_head_3136_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3212_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_leftCount_3181_; lean_object* v_rightCount_3182_; lean_object* v_val_3183_; lean_object* v_val_3184_; lean_object* v_fst_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3210_; 
v_leftCount_3181_ = lean_ctor_get(v_snd_3137_, 0);
lean_inc(v_leftCount_3181_);
v_rightCount_3182_ = lean_ctor_get(v_snd_3137_, 2);
lean_inc(v_rightCount_3182_);
lean_dec(v_snd_3137_);
v_val_3183_ = lean_ctor_get(v_leftIndex_3138_, 0);
lean_inc(v_val_3183_);
lean_dec_ref(v_leftIndex_3138_);
v_val_3184_ = lean_ctor_get(v_rightIndex_3139_, 0);
lean_inc(v_val_3184_);
lean_dec_ref(v_rightIndex_3139_);
v_fst_3185_ = lean_ctor_get(v_val_3172_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_val_3172_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_val_3172_, 1);
lean_dec(v_unused_3211_);
v___x_3187_ = v_val_3172_;
v_isShared_3188_ = v_isSharedCheck_3210_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_fst_3185_);
lean_dec(v_val_3172_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3210_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = lean_nat_add(v_leftCount_3181_, v_rightCount_3182_);
lean_dec(v_rightCount_3182_);
lean_dec(v_leftCount_3181_);
v___x_3190_ = lean_nat_dec_lt(v___x_3189_, v_fst_3185_);
lean_dec(v_fst_3185_);
if (v___x_3190_ == 0)
{
lean_dec(v___x_3189_);
lean_del_object(v___x_3187_);
lean_dec(v_val_3184_);
lean_dec(v_val_3183_);
lean_del_object(v___x_3179_);
lean_dec(v_fst_3177_);
lean_del_object(v___x_3175_);
v_as_x27_3134_ = v_tail_3173_;
goto _start;
}
else
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3208_; 
v_isSharedCheck_3208_ = !lean_is_exclusive(v_b_3135_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_b_3135_, 0);
lean_dec(v_unused_3209_);
v___x_3193_ = v_b_3135_;
v_isShared_3194_ = v_isSharedCheck_3208_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_b_3135_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3208_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 1, v_val_3184_);
lean_ctor_set(v___x_3187_, 0, v_val_3183_);
v___x_3196_ = v___x_3187_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_val_3183_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_val_3184_);
v___x_3196_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v___x_3196_);
v___x_3198_ = v___x_3179_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_fst_3177_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set_tag(v___x_3175_, 0);
lean_ctor_set(v___x_3175_, 1, v___x_3198_);
lean_ctor_set(v___x_3175_, 0, v___x_3189_);
v___x_3200_ = v___x_3175_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3200_);
v___x_3202_ = v___x_3193_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
v_as_x27_3134_ = v_tail_3173_;
v_b_3135_ = v___x_3202_;
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
lean_object* v_tail_3216_; 
lean_dec_ref(v_leftIndex_3138_);
lean_dec(v_rightIndex_3139_);
lean_dec(v_snd_3137_);
lean_dec(v_head_3136_);
v_tail_3216_ = lean_ctor_get(v_as_x27_3134_, 1);
lean_inc(v_tail_3216_);
lean_dec_ref(v_as_x27_3134_);
v_as_x27_3134_ = v_tail_3216_;
goto _start;
}
}
else
{
lean_object* v_tail_3218_; 
lean_dec(v_leftIndex_3138_);
lean_dec(v_snd_3137_);
lean_dec(v_head_3136_);
v_tail_3218_ = lean_ctor_get(v_as_x27_3134_, 1);
lean_inc(v_tail_3218_);
lean_dec_ref(v_as_x27_3134_);
v_as_x27_3134_ = v_tail_3218_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3220_, lean_object* v_index_3221_, lean_object* v_val_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3220_, v_val_3222_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_unsigned_to_nat(1u);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_index_3221_);
v___x_3228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3224_);
lean_ctor_set(v___x_3228_, 1, v___x_3225_);
lean_ctor_set(v___x_3228_, 2, v___x_3226_);
lean_ctor_set(v___x_3228_, 3, v___x_3227_);
v___x_3229_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3220_, v_val_3222_, v___x_3228_);
return v___x_3229_;
}
else
{
lean_object* v_val_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3251_; 
v_val_3230_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3232_ = v___x_3223_;
v_isShared_3233_ = v_isSharedCheck_3251_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_val_3230_);
lean_dec(v___x_3223_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3251_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v_leftCount_3234_; lean_object* v_leftIndex_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3248_; 
v_leftCount_3234_ = lean_ctor_get(v_val_3230_, 0);
v_leftIndex_3235_ = lean_ctor_get(v_val_3230_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_val_3230_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; lean_object* v_unused_3250_; 
v_unused_3249_ = lean_ctor_get(v_val_3230_, 3);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_val_3230_, 2);
lean_dec(v_unused_3250_);
v___x_3237_ = v_val_3230_;
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_leftIndex_3235_);
lean_inc(v_leftCount_3234_);
lean_dec(v_val_3230_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = lean_unsigned_to_nat(1u);
v___x_3240_ = lean_nat_add(v_leftCount_3234_, v___x_3239_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v_index_3221_);
v___x_3242_ = v___x_3232_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_index_3221_);
v___x_3242_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 3, v___x_3242_);
lean_ctor_set(v___x_3237_, 2, v___x_3240_);
v___x_3244_ = v___x_3237_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_leftCount_3234_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_leftIndex_3235_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; 
v___x_3245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3220_, v_val_3222_, v___x_3244_);
return v___x_3245_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3252_, lean_object* v___x_3253_, lean_object* v_fst_3254_, lean_object* v___x_3255_, lean_object* v_a_3256_, lean_object* v_b_3257_){
_start:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_nat_dec_lt(v_a_3256_, v_upperBound_3252_);
if (v___x_3258_ == 0)
{
lean_dec(v_a_3256_);
return v_b_3257_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3259_ = l_Subarray_get___redArg(v_fst_3254_, v_a_3256_);
lean_inc(v_a_3256_);
v___x_3260_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3257_, v_a_3256_, v___x_3259_);
v___x_3261_ = lean_unsigned_to_nat(1u);
v___x_3262_ = lean_nat_add(v_a_3256_, v___x_3261_);
lean_dec(v_a_3256_);
v_a_3256_ = v___x_3262_;
v_b_3257_ = v___x_3260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3264_, lean_object* v___x_3265_, lean_object* v_fst_3266_, lean_object* v___x_3267_, lean_object* v_a_3268_, lean_object* v_b_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3264_, v___x_3265_, v_fst_3266_, v___x_3267_, v_a_3268_, v_b_3269_);
lean_dec(v___x_3267_);
lean_dec_ref(v_fst_3266_);
lean_dec(v___x_3265_);
lean_dec(v_upperBound_3264_);
return v_res_3270_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_unsigned_to_nat(16u);
v___x_3273_ = lean_mk_array(v___x_3272_, v___x_3271_);
return v___x_3273_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v_hist_3276_; 
v___x_3274_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3275_ = lean_unsigned_to_nat(0u);
v_hist_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3276_, 0, v___x_3275_);
lean_ctor_set(v_hist_3276_, 1, v___x_3274_);
return v_hist_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3277_, lean_object* v_right_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v_snd_3280_; lean_object* v_fst_3281_; lean_object* v_fst_3282_; lean_object* v_snd_3283_; lean_object* v___x_3284_; lean_object* v_snd_3285_; lean_object* v_fst_3286_; lean_object* v_fst_3287_; lean_object* v_snd_3288_; lean_object* v_start_3289_; lean_object* v_stop_3290_; lean_object* v___x_3291_; lean_object* v_hist_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_start_3295_; lean_object* v_stop_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v_buckets_3299_; lean_object* v___x_3300_; lean_object* v___y_3302_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3279_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3277_, v_right_3278_);
v_snd_3280_ = lean_ctor_get(v___x_3279_, 1);
lean_inc(v_snd_3280_);
v_fst_3281_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_fst_3281_);
lean_dec_ref(v___x_3279_);
v_fst_3282_ = lean_ctor_get(v_snd_3280_, 0);
lean_inc(v_fst_3282_);
v_snd_3283_ = lean_ctor_get(v_snd_3280_, 1);
lean_inc(v_snd_3283_);
lean_dec(v_snd_3280_);
v___x_3284_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3282_, v_snd_3283_);
v_snd_3285_ = lean_ctor_get(v___x_3284_, 1);
lean_inc(v_snd_3285_);
v_fst_3286_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_fst_3286_);
lean_dec_ref(v___x_3284_);
v_fst_3287_ = lean_ctor_get(v_snd_3285_, 0);
lean_inc(v_fst_3287_);
v_snd_3288_ = lean_ctor_get(v_snd_3285_, 1);
lean_inc(v_snd_3288_);
lean_dec(v_snd_3285_);
v_start_3289_ = lean_ctor_get(v_fst_3286_, 1);
v_stop_3290_ = lean_ctor_get(v_fst_3286_, 2);
v___x_3291_ = lean_unsigned_to_nat(0u);
v_hist_3292_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3293_ = lean_nat_sub(v_stop_3290_, v_start_3289_);
v___x_3294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3293_, v_fst_3287_, v___x_3293_, v_fst_3286_, v___x_3291_, v_hist_3292_);
v_start_3295_ = lean_ctor_get(v_fst_3287_, 1);
v_stop_3296_ = lean_ctor_get(v_fst_3287_, 2);
v___x_3297_ = lean_nat_sub(v_stop_3296_, v_start_3295_);
v___x_3298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3297_, v___x_3297_, v_fst_3287_, v___x_3293_, v___x_3291_, v___x_3294_);
lean_dec(v___x_3293_);
lean_dec(v___x_3297_);
v_buckets_3299_ = lean_ctor_get(v___x_3298_, 1);
lean_inc_ref(v_buckets_3299_);
lean_dec_ref(v___x_3298_);
v___x_3300_ = lean_box(0);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_array_get_size(v_buckets_3299_);
v___x_3330_ = lean_nat_dec_lt(v___x_3291_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_dec_ref(v_buckets_3299_);
v___y_3302_ = v___x_3328_;
goto v___jp_3301_;
}
else
{
size_t v___x_3331_; size_t v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_usize_of_nat(v___x_3329_);
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3299_, v___x_3331_, v___x_3332_, v___x_3328_);
lean_dec_ref(v_buckets_3299_);
v___y_3302_ = v___x_3333_;
goto v___jp_3301_;
}
v___jp_3301_:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3302_, v___x_3300_);
if (lean_obj_tag(v___x_3303_) == 1)
{
lean_object* v_val_3304_; lean_object* v_snd_3305_; lean_object* v_snd_3306_; lean_object* v_fst_3307_; lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3310_; lean_object* v_fst_3311_; lean_object* v_snd_3312_; lean_object* v___x_3313_; lean_object* v_fst_3314_; lean_object* v_snd_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_val_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_val_3304_);
lean_dec_ref(v___x_3303_);
v_snd_3305_ = lean_ctor_get(v_val_3304_, 1);
lean_inc(v_snd_3305_);
lean_dec(v_val_3304_);
v_snd_3306_ = lean_ctor_get(v_snd_3305_, 1);
lean_inc(v_snd_3306_);
v_fst_3307_ = lean_ctor_get(v_snd_3305_, 0);
lean_inc(v_fst_3307_);
lean_dec(v_snd_3305_);
v_fst_3308_ = lean_ctor_get(v_snd_3306_, 0);
lean_inc(v_fst_3308_);
v_snd_3309_ = lean_ctor_get(v_snd_3306_, 1);
lean_inc(v_snd_3309_);
lean_dec(v_snd_3306_);
v___x_3310_ = l_Subarray_split___redArg(v_fst_3286_, v_fst_3308_);
lean_dec(v_fst_3308_);
v_fst_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_fst_3311_);
v_snd_3312_ = lean_ctor_get(v___x_3310_, 1);
lean_inc(v_snd_3312_);
lean_dec_ref(v___x_3310_);
v___x_3313_ = l_Subarray_split___redArg(v_fst_3287_, v_snd_3309_);
lean_dec(v_snd_3309_);
v_fst_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_fst_3314_);
v_snd_3315_ = lean_ctor_get(v___x_3313_, 1);
lean_inc(v_snd_3315_);
lean_dec_ref(v___x_3313_);
v___x_3316_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3311_, v_fst_3314_);
v___x_3317_ = l_Array_append___redArg(v_fst_3281_, v___x_3316_);
lean_dec_ref(v___x_3316_);
v___x_3318_ = lean_unsigned_to_nat(1u);
v___x_3319_ = lean_mk_empty_array_with_capacity(v___x_3318_);
v___x_3320_ = lean_array_push(v___x_3319_, v_fst_3307_);
v___x_3321_ = l_Array_append___redArg(v___x_3317_, v___x_3320_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = l_Subarray_drop___redArg(v_snd_3312_, v___x_3318_);
v___x_3323_ = l_Subarray_drop___redArg(v_snd_3315_, v___x_3318_);
v___x_3324_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3322_, v___x_3323_);
v___x_3325_ = l_Array_append___redArg(v___x_3321_, v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = l_Array_append___redArg(v___x_3325_, v_snd_3288_);
lean_dec(v_snd_3288_);
return v___x_3326_;
}
else
{
lean_object* v___x_3327_; 
lean_dec(v___x_3303_);
lean_dec(v_fst_3287_);
lean_dec(v_fst_3286_);
v___x_3327_ = l_Array_append___redArg(v_fst_3281_, v_snd_3288_);
lean_dec(v_snd_3288_);
return v___x_3327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3334_, lean_object* v_original_3335_, lean_object* v_b_3336_){
_start:
{
lean_object* v_fst_3337_; lean_object* v_snd_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3357_; 
v_fst_3337_ = lean_ctor_get(v_b_3336_, 0);
v_snd_3338_ = lean_ctor_get(v_b_3336_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_b_3336_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3340_ = v_b_3336_;
v_isShared_3341_ = v_isSharedCheck_3357_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snd_3338_);
lean_inc(v_fst_3337_);
lean_dec(v_b_3336_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3357_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_nat_dec_lt(v_snd_3338_, v___x_3334_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3344_; 
if (v_isShared_3341_ == 0)
{
v___x_3344_ = v___x_3340_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_fst_3337_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_snd_3338_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
else
{
uint8_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3346_ = 1;
v___x_3347_ = lean_array_fget_borrowed(v_original_3335_, v_snd_3338_);
v___x_3348_ = lean_box(v___x_3346_);
lean_inc(v___x_3347_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v___x_3347_);
lean_ctor_set(v___x_3340_, 0, v___x_3348_);
v___x_3350_ = v___x_3340_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3347_);
v___x_3350_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3351_ = lean_array_push(v_fst_3337_, v___x_3350_);
v___x_3352_ = lean_unsigned_to_nat(1u);
v___x_3353_ = lean_nat_add(v_snd_3338_, v___x_3352_);
lean_dec(v_snd_3338_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3351_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v_b_3336_ = v___x_3354_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3358_, lean_object* v_original_3359_, lean_object* v_b_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3358_, v_original_3359_, v_b_3360_);
lean_dec_ref(v_original_3359_);
lean_dec(v___x_3358_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3362_, size_t v_i_3363_, lean_object* v_bs_3364_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3363_, v_sz_3362_);
if (v___x_3365_ == 0)
{
return v_bs_3364_;
}
else
{
lean_object* v_v_3366_; lean_object* v___x_3367_; lean_object* v_bs_x27_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; size_t v___x_3372_; size_t v___x_3373_; lean_object* v___x_3374_; 
v_v_3366_ = lean_array_uget(v_bs_3364_, v_i_3363_);
v___x_3367_ = lean_unsigned_to_nat(0u);
v_bs_x27_3368_ = lean_array_uset(v_bs_3364_, v_i_3363_, v___x_3367_);
v___x_3369_ = 0;
v___x_3370_ = lean_box(v___x_3369_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
lean_ctor_set(v___x_3371_, 1, v_v_3366_);
v___x_3372_ = ((size_t)1ULL);
v___x_3373_ = lean_usize_add(v_i_3363_, v___x_3372_);
v___x_3374_ = lean_array_uset(v_bs_x27_3368_, v_i_3363_, v___x_3371_);
v_i_3363_ = v___x_3373_;
v_bs_3364_ = v___x_3374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3376_, lean_object* v_i_3377_, lean_object* v_bs_3378_){
_start:
{
size_t v_sz_boxed_3379_; size_t v_i_boxed_3380_; lean_object* v_res_3381_; 
v_sz_boxed_3379_ = lean_unbox_usize(v_sz_3376_);
lean_dec(v_sz_3376_);
v_i_boxed_3380_ = lean_unbox_usize(v_i_3377_);
lean_dec(v_i_3377_);
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3379_, v_i_boxed_3380_, v_bs_3378_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3382_, size_t v_i_3383_, lean_object* v_bs_3384_){
_start:
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_usize_dec_lt(v_i_3383_, v_sz_3382_);
if (v___x_3385_ == 0)
{
return v_bs_3384_;
}
else
{
lean_object* v_v_3386_; lean_object* v___x_3387_; lean_object* v_bs_x27_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v_v_3386_ = lean_array_uget(v_bs_3384_, v_i_3383_);
v___x_3387_ = lean_unsigned_to_nat(0u);
v_bs_x27_3388_ = lean_array_uset(v_bs_3384_, v_i_3383_, v___x_3387_);
v___x_3389_ = 1;
v___x_3390_ = lean_box(v___x_3389_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v_v_3386_);
v___x_3392_ = ((size_t)1ULL);
v___x_3393_ = lean_usize_add(v_i_3383_, v___x_3392_);
v___x_3394_ = lean_array_uset(v_bs_x27_3388_, v_i_3383_, v___x_3391_);
v_i_3383_ = v___x_3393_;
v_bs_3384_ = v___x_3394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3396_, lean_object* v_i_3397_, lean_object* v_bs_3398_){
_start:
{
size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3399_, v_i_boxed_3400_, v_bs_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3409_, lean_object* v_edited_3410_){
_start:
{
lean_object* v_i_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_i_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = lean_array_get_size(v_original_3409_);
v___x_3413_ = lean_nat_dec_lt(v_i_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
size_t v_sz_3414_; size_t v___x_3415_; lean_object* v___x_3416_; 
lean_dec_ref(v_original_3409_);
v_sz_3414_ = lean_array_size(v_edited_3410_);
v___x_3415_ = ((size_t)0ULL);
v___x_3416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3414_, v___x_3415_, v_edited_3410_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_array_get_size(v_edited_3410_);
v___x_3418_ = lean_nat_dec_lt(v_i_3411_, v___x_3417_);
if (v___x_3418_ == 0)
{
size_t v_sz_3419_; size_t v___x_3420_; lean_object* v___x_3421_; 
lean_dec_ref(v_edited_3410_);
v_sz_3419_ = lean_array_size(v_original_3409_);
v___x_3420_ = ((size_t)0ULL);
v___x_3421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3419_, v___x_3420_, v_original_3409_);
return v___x_3421_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v_ds_3424_; lean_object* v___x_3425_; size_t v_sz_3426_; size_t v___x_3427_; lean_object* v___x_3428_; lean_object* v_snd_3429_; lean_object* v_fst_3430_; lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3451_; 
lean_inc_ref(v_original_3409_);
v___x_3422_ = l_Array_toSubarray___redArg(v_original_3409_, v_i_3411_, v___x_3412_);
lean_inc_ref(v_edited_3410_);
v___x_3423_ = l_Array_toSubarray___redArg(v_edited_3410_, v_i_3411_, v___x_3417_);
v_ds_3424_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3422_, v___x_3423_);
v___x_3425_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3426_ = lean_array_size(v_ds_3424_);
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3410_, v___x_3417_, v_original_3409_, v___x_3412_, v_ds_3424_, v_sz_3426_, v___x_3427_, v___x_3425_);
lean_dec_ref(v_ds_3424_);
v_snd_3429_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_snd_3429_);
v_fst_3430_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_fst_3430_);
lean_dec_ref(v___x_3428_);
v_fst_3431_ = lean_ctor_get(v_snd_3429_, 0);
v_snd_3432_ = lean_ctor_get(v_snd_3429_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_snd_3429_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3434_ = v_snd_3429_;
v_isShared_3435_ = v_isSharedCheck_3451_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_inc(v_fst_3431_);
lean_dec(v_snd_3429_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3451_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v_fst_3431_);
lean_ctor_set(v___x_3434_, 0, v_fst_3430_);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_fst_3431_);
v___x_3437_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3438_; lean_object* v_fst_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3448_; 
v___x_3438_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3412_, v_original_3409_, v___x_3437_);
lean_dec_ref(v_original_3409_);
v_fst_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v___x_3438_, 1);
lean_dec(v_unused_3449_);
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_fst_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v_snd_3432_);
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_fst_3439_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_snd_3432_);
v___x_3444_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; lean_object* v_fst_3446_; 
v___x_3445_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3417_, v_edited_3410_, v___x_3444_);
lean_dec_ref(v_edited_3410_);
v_fst_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_fst_3446_);
lean_dec_ref(v___x_3445_);
return v_fst_3446_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_){
_start:
{
if (lean_obj_tag(v_x_3453_) == 0)
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = l_List_reverse___redArg(v_x_3454_);
v___x_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
else
{
lean_object* v_head_3458_; lean_object* v_tail_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3468_; 
v_head_3458_ = lean_ctor_get(v_x_3453_, 0);
v_tail_3459_ = lean_ctor_get(v_x_3453_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_x_3453_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3461_ = v_x_3453_;
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_tail_3459_);
lean_inc(v_head_3458_);
lean_dec(v_x_3453_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3458_, v___y_3452_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 1, v_x_3454_);
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_x_3454_);
v___x_3465_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
v_x_3453_ = v_tail_3459_;
v_x_3454_ = v___x_3465_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3469_, lean_object* v_x_3470_, lean_object* v_x_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3469_, v_x_3470_, v_x_3471_);
lean_dec(v___y_3469_);
return v_res_3473_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3476_ = l_Lean_stringToMessageData(v___x_3475_);
return v___x_3476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = l_Lean_MessageLog_empty;
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; uint8_t v___y_3535_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; uint8_t v___y_3604_; uint8_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v_dc_x3f_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3490_);
v___x_3739_ = l_Lean_Syntax_isOfKind(v_x_3490_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; 
lean_dec(v_x_3490_);
v___x_3740_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3740_;
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v___x_3741_ = lean_unsigned_to_nat(0u);
v___x_3742_ = l_Lean_Syntax_getArg(v_x_3490_, v___x_3741_);
v___x_3743_ = l_Lean_Syntax_isNone(v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3744_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3742_);
v___x_3745_ = l_Lean_Syntax_matchesNull(v___x_3742_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
lean_dec(v___x_3742_);
lean_dec(v_x_3490_);
v___x_3746_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3746_;
}
else
{
lean_object* v_dc_x3f_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v_dc_x3f_3747_ = l_Lean_Syntax_getArg(v___x_3742_, v___x_3741_);
lean_dec(v___x_3742_);
v___x_3748_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3747_);
v___x_3749_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3747_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; 
lean_dec(v_dc_x3f_3747_);
lean_dec(v_x_3490_);
v___x_3750_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3750_;
}
else
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3751_, 0, v_dc_x3f_3747_);
v_dc_x3f_3719_ = v___x_3751_;
v___y_3720_ = v_a_3491_;
v___y_3721_ = v_a_3492_;
goto v___jp_3718_;
}
}
}
else
{
lean_object* v___x_3752_; 
lean_dec(v___x_3742_);
v___x_3752_ = lean_box(0);
v_dc_x3f_3719_ = v___x_3752_;
v___y_3720_ = v_a_3491_;
v___y_3721_ = v_a_3492_;
goto v___jp_3718_;
}
}
v___jp_3494_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3500_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3501_ = l_Lean_stringToMessageData(v___y_3499_);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3497_, v___x_3502_, v___y_3496_, v___y_3498_);
lean_dec(v___y_3497_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3524_; 
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; 
v_unused_3525_ = lean_ctor_get(v___x_3503_, 0);
lean_dec(v_unused_3525_);
v___x_3505_ = v___x_3503_;
v_isShared_3506_ = v_isSharedCheck_3524_;
goto v_resetjp_3504_;
}
else
{
lean_dec(v___x_3503_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3524_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; 
v___x_3507_ = l_Lean_Elab_Command_getRef___redArg(v___y_3496_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3507_);
v___x_3509_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
lean_ctor_set(v___x_3510_, 1, v___y_3495_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3508_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set_tag(v___x_3505_, 10);
lean_ctor_set(v___x_3505_, 0, v___x_3511_);
v___x_3513_ = v___x_3505_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3513_, v___y_3496_, v___y_3498_);
return v___x_3514_;
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_3505_);
lean_dec_ref(v___y_3495_);
v_a_3516_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3507_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3507_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3495_);
return v___x_3503_;
}
}
v___jp_3526_:
{
if (v___y_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v_env_3537_; lean_object* v_scopes_3538_; lean_object* v_usedQuotCtxts_3539_; lean_object* v_nextMacroScope_3540_; lean_object* v_maxRecDepth_3541_; lean_object* v_ngen_3542_; lean_object* v_auxDeclNGen_3543_; lean_object* v_infoState_3544_; lean_object* v_traceState_3545_; lean_object* v_snapshotTasks_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3572_; 
lean_dec(v___y_3533_);
v___x_3536_ = lean_st_ref_take(v___y_3534_);
v_env_3537_ = lean_ctor_get(v___x_3536_, 0);
v_scopes_3538_ = lean_ctor_get(v___x_3536_, 2);
v_usedQuotCtxts_3539_ = lean_ctor_get(v___x_3536_, 3);
v_nextMacroScope_3540_ = lean_ctor_get(v___x_3536_, 4);
v_maxRecDepth_3541_ = lean_ctor_get(v___x_3536_, 5);
v_ngen_3542_ = lean_ctor_get(v___x_3536_, 6);
v_auxDeclNGen_3543_ = lean_ctor_get(v___x_3536_, 7);
v_infoState_3544_ = lean_ctor_get(v___x_3536_, 8);
v_traceState_3545_ = lean_ctor_get(v___x_3536_, 9);
v_snapshotTasks_3546_ = lean_ctor_get(v___x_3536_, 10);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v___x_3536_, 1);
lean_dec(v_unused_3573_);
v___x_3548_ = v___x_3536_;
v_isShared_3549_ = v_isSharedCheck_3572_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_snapshotTasks_3546_);
lean_inc(v_traceState_3545_);
lean_inc(v_infoState_3544_);
lean_inc(v_auxDeclNGen_3543_);
lean_inc(v_ngen_3542_);
lean_inc(v_maxRecDepth_3541_);
lean_inc(v_nextMacroScope_3540_);
lean_inc(v_usedQuotCtxts_3539_);
lean_inc(v_scopes_3538_);
lean_inc(v_env_3537_);
lean_dec(v___x_3536_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3572_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 1, v___y_3532_);
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_env_3537_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___y_3532_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_scopes_3538_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_usedQuotCtxts_3539_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_nextMacroScope_3540_);
lean_ctor_set(v_reuseFailAlloc_3571_, 5, v_maxRecDepth_3541_);
lean_ctor_set(v_reuseFailAlloc_3571_, 6, v_ngen_3542_);
lean_ctor_set(v_reuseFailAlloc_3571_, 7, v_auxDeclNGen_3543_);
lean_ctor_set(v_reuseFailAlloc_3571_, 8, v_infoState_3544_);
lean_ctor_set(v_reuseFailAlloc_3571_, 9, v_traceState_3545_);
lean_ctor_set(v_reuseFailAlloc_3571_, 10, v_snapshotTasks_3546_);
v___x_3551_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v_scopes_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v_opts_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3552_ = lean_st_ref_set(v___y_3534_, v___x_3551_);
v___x_3553_ = lean_st_ref_get(v___y_3534_);
v_scopes_3554_ = lean_ctor_get(v___x_3553_, 2);
lean_inc(v_scopes_3554_);
lean_dec(v___x_3553_);
v___x_3555_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3556_ = l_List_head_x21___redArg(v___x_3555_, v_scopes_3554_);
lean_dec(v_scopes_3554_);
v_opts_3557_ = lean_ctor_get(v___x_3556_, 1);
lean_inc_ref(v_opts_3557_);
lean_dec(v___x_3556_);
v___x_3558_ = l_guard__msgs_diff;
v___x_3559_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3557_, v___x_3558_);
lean_dec_ref(v_opts_3557_);
if (v___x_3559_ == 0)
{
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3527_);
lean_inc_ref(v___y_3529_);
v___y_3495_ = v___y_3529_;
v___y_3496_ = v___y_3528_;
v___y_3497_ = v___y_3531_;
v___y_3498_ = v___y_3534_;
v___y_3499_ = v___y_3529_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3560_ = lean_string_utf8_byte_size(v___y_3530_);
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3530_);
v___x_3561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3561_, 0, v___y_3530_);
lean_ctor_set(v___x_3561_, 1, v___y_3527_);
lean_ctor_set(v___x_3561_, 2, v___x_3560_);
v___x_3562_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3561_);
v___x_3563_ = lean_mk_empty_array_with_capacity(v___y_3527_);
lean_inc_ref(v___x_3563_);
v___x_3564_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3530_, v___x_3561_, v___x_3560_, v___x_3562_, v___x_3563_);
lean_dec_ref(v___x_3561_);
v___x_3565_ = lean_string_utf8_byte_size(v___y_3529_);
lean_inc_ref_n(v___y_3529_, 2);
v___x_3566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3566_, 0, v___y_3529_);
lean_ctor_set(v___x_3566_, 1, v___y_3527_);
lean_ctor_set(v___x_3566_, 2, v___x_3565_);
v___x_3567_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3566_);
v___x_3568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3529_, v___x_3566_, v___x_3565_, v___x_3567_, v___x_3563_);
lean_dec_ref(v___x_3566_);
v___x_3569_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3564_, v___x_3568_);
v___x_3570_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3569_);
lean_dec_ref(v___x_3569_);
v___y_3495_ = v___y_3529_;
v___y_3496_ = v___y_3528_;
v___y_3497_ = v___y_3531_;
v___y_3498_ = v___y_3534_;
v___y_3499_ = v___x_3570_;
goto v___jp_3494_;
}
}
}
}
else
{
lean_object* v___x_3574_; lean_object* v_env_3575_; lean_object* v_scopes_3576_; lean_object* v_usedQuotCtxts_3577_; lean_object* v_nextMacroScope_3578_; lean_object* v_maxRecDepth_3579_; lean_object* v_ngen_3580_; lean_object* v_auxDeclNGen_3581_; lean_object* v_infoState_3582_; lean_object* v_traceState_3583_; lean_object* v_snapshotTasks_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3527_);
v___x_3574_ = lean_st_ref_take(v___y_3534_);
v_env_3575_ = lean_ctor_get(v___x_3574_, 0);
v_scopes_3576_ = lean_ctor_get(v___x_3574_, 2);
v_usedQuotCtxts_3577_ = lean_ctor_get(v___x_3574_, 3);
v_nextMacroScope_3578_ = lean_ctor_get(v___x_3574_, 4);
v_maxRecDepth_3579_ = lean_ctor_get(v___x_3574_, 5);
v_ngen_3580_ = lean_ctor_get(v___x_3574_, 6);
v_auxDeclNGen_3581_ = lean_ctor_get(v___x_3574_, 7);
v_infoState_3582_ = lean_ctor_get(v___x_3574_, 8);
v_traceState_3583_ = lean_ctor_get(v___x_3574_, 9);
v_snapshotTasks_3584_ = lean_ctor_get(v___x_3574_, 10);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v___x_3574_, 1);
lean_dec(v_unused_3595_);
v___x_3586_ = v___x_3574_;
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snapshotTasks_3584_);
lean_inc(v_traceState_3583_);
lean_inc(v_infoState_3582_);
lean_inc(v_auxDeclNGen_3581_);
lean_inc(v_ngen_3580_);
lean_inc(v_maxRecDepth_3579_);
lean_inc(v_nextMacroScope_3578_);
lean_inc(v_usedQuotCtxts_3577_);
lean_inc(v_scopes_3576_);
lean_inc(v_env_3575_);
lean_dec(v___x_3574_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___y_3533_);
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_env_3575_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v___y_3533_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_scopes_3576_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_usedQuotCtxts_3577_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_nextMacroScope_3578_);
lean_ctor_set(v_reuseFailAlloc_3593_, 5, v_maxRecDepth_3579_);
lean_ctor_set(v_reuseFailAlloc_3593_, 6, v_ngen_3580_);
lean_ctor_set(v_reuseFailAlloc_3593_, 7, v_auxDeclNGen_3581_);
lean_ctor_set(v_reuseFailAlloc_3593_, 8, v_infoState_3582_);
lean_ctor_set(v_reuseFailAlloc_3593_, 9, v_traceState_3583_);
lean_ctor_set(v_reuseFailAlloc_3593_, 10, v_snapshotTasks_3584_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = lean_st_ref_set(v___y_3534_, v___x_3589_);
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
}
}
v___jp_3596_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v_str_3619_; lean_object* v_startInclusive_3620_; lean_object* v_endExclusive_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3636_; 
v___x_3609_ = l_Lean_MessageLog_toList(v___y_3598_);
lean_dec(v___y_3598_);
v___x_3610_ = lean_box(0);
v___x_3611_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3608_, v___x_3609_, v___x_3610_);
lean_dec(v___y_3608_);
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3601_, v_a_3612_);
v___x_3614_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3615_ = l_String_intercalate(v___x_3614_, v___x_3613_);
v___x_3616_ = lean_string_utf8_byte_size(v___x_3615_);
lean_inc(v___y_3597_);
v___x_3617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___y_3597_);
lean_ctor_set(v___x_3617_, 2, v___x_3616_);
v___x_3618_ = l_String_Slice_trimAscii(v___x_3617_);
v_str_3619_ = lean_ctor_get(v___x_3618_, 0);
v_startInclusive_3620_ = lean_ctor_get(v___x_3618_, 1);
v_endExclusive_3621_ = lean_ctor_get(v___x_3618_, 2);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3623_ = v___x_3618_;
v_isShared_3624_ = v_isSharedCheck_3636_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_endExclusive_3621_);
lean_inc(v_startInclusive_3620_);
lean_inc(v_str_3619_);
lean_dec(v___x_3618_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3636_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_string_utf8_extract(v_str_3619_, v_startInclusive_3620_, v_endExclusive_3621_);
lean_dec(v_endExclusive_3621_);
lean_dec(v_startInclusive_3620_);
lean_dec_ref(v_str_3619_);
if (v___y_3605_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
lean_del_object(v___x_3623_);
lean_inc_ref(v___y_3600_);
v___x_3626_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3604_, v___y_3600_);
lean_inc_ref(v___x_3625_);
v___x_3627_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3604_, v___x_3625_);
v___x_3628_ = lean_string_dec_eq(v___x_3626_, v___x_3627_);
lean_dec_ref(v___x_3627_);
lean_dec_ref(v___x_3626_);
v___y_3527_ = v___y_3597_;
v___y_3528_ = v___y_3599_;
v___y_3529_ = v___x_3625_;
v___y_3530_ = v___y_3600_;
v___y_3531_ = v___y_3602_;
v___y_3532_ = v___y_3603_;
v___y_3533_ = v___y_3606_;
v___y_3534_ = v___y_3607_;
v___y_3535_ = v___x_3628_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
lean_inc_ref(v___x_3625_);
v___x_3629_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3604_, v___x_3625_);
lean_inc_ref(v___y_3600_);
v___x_3630_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3604_, v___y_3600_);
v___x_3631_ = lean_string_utf8_byte_size(v___x_3629_);
lean_inc(v___y_3597_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 2, v___x_3631_);
lean_ctor_set(v___x_3623_, 1, v___y_3597_);
lean_ctor_set(v___x_3623_, 0, v___x_3629_);
v___x_3633_ = v___x_3623_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v___y_3597_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
uint8_t v___x_3634_; 
v___x_3634_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3630_, v___x_3633_);
lean_dec_ref(v___x_3633_);
v___y_3527_ = v___y_3597_;
v___y_3528_ = v___y_3599_;
v___y_3529_ = v___x_3625_;
v___y_3530_ = v___y_3600_;
v___y_3531_ = v___y_3602_;
v___y_3532_ = v___y_3603_;
v___y_3533_ = v___y_3606_;
v___y_3534_ = v___y_3607_;
v___y_3535_ = v___x_3634_;
goto v___jp_3526_;
}
}
}
}
v___jp_3637_:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3640_, v___y_3638_, v___y_3642_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v_filterFn_3646_; uint8_t v_whitespace_3647_; uint8_t v_ordering_3648_; uint8_t v_reportPositions_3649_; uint8_t v_substring_3650_; lean_object* v___x_3651_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
v_filterFn_3646_ = lean_ctor_get(v_a_3645_, 0);
lean_inc_ref(v_filterFn_3646_);
v_whitespace_3647_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*1);
v_ordering_3648_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*1 + 1);
v_reportPositions_3649_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*1 + 2);
v_substring_3650_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*1 + 3);
lean_dec(v_a_3645_);
v___x_3651_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3639_, v___y_3638_, v___y_3642_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_a_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_str_3661_; lean_object* v_startInclusive_3662_; lean_object* v_endExclusive_3663_; lean_object* v_fst_3664_; lean_object* v_snd_3665_; lean_object* v_fileMap_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref(v___x_3651_);
v___x_3653_ = l_Lean_MessageLog_toList(v_a_3652_);
v___x_3654_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3655_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3646_, v___x_3653_, v___x_3654_);
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref(v___x_3655_);
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = lean_string_utf8_byte_size(v___y_3643_);
v___x_3659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3659_, 0, v___y_3643_);
lean_ctor_set(v___x_3659_, 1, v___x_3657_);
lean_ctor_set(v___x_3659_, 2, v___x_3658_);
v___x_3660_ = l_String_Slice_trimAscii(v___x_3659_);
v_str_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc_ref(v_str_3661_);
v_startInclusive_3662_ = lean_ctor_get(v___x_3660_, 1);
lean_inc(v_startInclusive_3662_);
v_endExclusive_3663_ = lean_ctor_get(v___x_3660_, 2);
lean_inc(v_endExclusive_3663_);
lean_dec_ref(v___x_3660_);
v_fst_3664_ = lean_ctor_get(v_a_3656_, 0);
lean_inc(v_fst_3664_);
v_snd_3665_ = lean_ctor_get(v_a_3656_, 1);
lean_inc(v_snd_3665_);
lean_dec(v_a_3656_);
v_fileMap_3666_ = lean_ctor_get(v___y_3638_, 1);
v___x_3667_ = lean_string_utf8_extract(v_str_3661_, v_startInclusive_3662_, v_endExclusive_3663_);
lean_dec(v_endExclusive_3663_);
lean_dec(v_startInclusive_3662_);
lean_dec_ref(v_str_3661_);
v___x_3668_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3667_);
if (v_reportPositions_3649_ == 0)
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_box(0);
v___y_3597_ = v___x_3657_;
v___y_3598_ = v_fst_3664_;
v___y_3599_ = v___y_3638_;
v___y_3600_ = v___x_3668_;
v___y_3601_ = v_ordering_3648_;
v___y_3602_ = v___y_3641_;
v___y_3603_ = v_a_3652_;
v___y_3604_ = v_whitespace_3647_;
v___y_3605_ = v_substring_3650_;
v___y_3606_ = v_snd_3665_;
v___y_3607_ = v___y_3642_;
v___y_3608_ = v___x_3669_;
goto v___jp_3596_;
}
else
{
uint8_t v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = 0;
v___x_3671_ = l_Lean_Syntax_getPos_x3f(v___y_3641_, v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_box(0);
v___y_3597_ = v___x_3657_;
v___y_3598_ = v_fst_3664_;
v___y_3599_ = v___y_3638_;
v___y_3600_ = v___x_3668_;
v___y_3601_ = v_ordering_3648_;
v___y_3602_ = v___y_3641_;
v___y_3603_ = v_a_3652_;
v___y_3604_ = v_whitespace_3647_;
v___y_3605_ = v_substring_3650_;
v___y_3606_ = v_snd_3665_;
v___y_3607_ = v___y_3642_;
v___y_3608_ = v___x_3672_;
goto v___jp_3596_;
}
else
{
lean_object* v_val_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3682_; 
v_val_3673_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3675_ = v___x_3671_;
v_isShared_3676_ = v_isSharedCheck_3682_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_val_3673_);
lean_dec(v___x_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3682_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v_line_3678_; lean_object* v___x_3680_; 
lean_inc_ref(v_fileMap_3666_);
v___x_3677_ = l_Lean_FileMap_toPosition(v_fileMap_3666_, v_val_3673_);
lean_dec(v_val_3673_);
v_line_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_line_3678_);
lean_dec_ref(v___x_3677_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_line_3678_);
v___x_3680_ = v___x_3675_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_line_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
v___y_3597_ = v___x_3657_;
v___y_3598_ = v_fst_3664_;
v___y_3599_ = v___y_3638_;
v___y_3600_ = v___x_3668_;
v___y_3601_ = v_ordering_3648_;
v___y_3602_ = v___y_3641_;
v___y_3603_ = v_a_3652_;
v___y_3604_ = v_whitespace_3647_;
v___y_3605_ = v_substring_3650_;
v___y_3606_ = v_snd_3665_;
v___y_3607_ = v___y_3642_;
v___y_3608_ = v___x_3680_;
goto v___jp_3596_;
}
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v_filterFn_3646_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3641_);
v_a_3683_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3651_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3651_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3641_);
lean_dec(v___y_3639_);
v_a_3691_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3644_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3644_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
v___jp_3699_:
{
if (lean_obj_tag(v___y_3703_) == 0)
{
lean_object* v___x_3706_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3638_ = v___y_3700_;
v___y_3639_ = v___y_3701_;
v___y_3640_ = v___y_3705_;
v___y_3641_ = v___y_3702_;
v___y_3642_ = v___y_3704_;
v___y_3643_ = v___x_3706_;
goto v___jp_3637_;
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3708_; 
v_val_3707_ = lean_ctor_get(v___y_3703_, 0);
lean_inc(v_val_3707_);
lean_dec_ref(v___y_3703_);
v___x_3708_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3707_, v___y_3700_, v___y_3704_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref(v___x_3708_);
v___y_3638_ = v___y_3700_;
v___y_3639_ = v___y_3701_;
v___y_3640_ = v___y_3705_;
v___y_3641_ = v___y_3702_;
v___y_3642_ = v___y_3704_;
v___y_3643_ = v_a_3709_;
goto v___jp_3637_;
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v___y_3705_);
lean_dec(v___y_3702_);
lean_dec(v___y_3701_);
v_a_3710_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3708_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3708_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
v___jp_3718_:
{
lean_object* v___x_3722_; lean_object* v_tk_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3722_ = lean_unsigned_to_nat(1u);
v_tk_3723_ = l_Lean_Syntax_getArg(v_x_3490_, v___x_3722_);
v___x_3724_ = lean_unsigned_to_nat(2u);
v___x_3725_ = l_Lean_Syntax_getArg(v_x_3490_, v___x_3724_);
v___x_3726_ = lean_unsigned_to_nat(4u);
v___x_3727_ = l_Lean_Syntax_getArg(v_x_3490_, v___x_3726_);
lean_dec(v_x_3490_);
v___x_3728_ = l_Lean_Syntax_getOptional_x3f(v___x_3725_);
lean_dec(v___x_3725_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_box(0);
v___y_3700_ = v___y_3720_;
v___y_3701_ = v___x_3727_;
v___y_3702_ = v_tk_3723_;
v___y_3703_ = v_dc_x3f_3719_;
v___y_3704_ = v___y_3721_;
v___y_3705_ = v___x_3729_;
goto v___jp_3699_;
}
else
{
lean_object* v_val_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_val_3730_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3728_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_val_3730_);
lean_dec(v___x_3728_);
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
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_val_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
v___y_3700_ = v___y_3720_;
v___y_3701_ = v___x_3727_;
v___y_3702_ = v_tk_3723_;
v___y_3703_ = v_dc_x3f_3719_;
v___y_3704_ = v___y_3721_;
v___y_3705_ = v___x_3735_;
goto v___jp_3699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3753_, v_a_3754_, v_a_3755_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3754_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3758_, lean_object* v_as_3759_, lean_object* v_as_x27_3760_, lean_object* v_b_3761_, lean_object* v_a_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3758_, v_as_x27_3760_, v_b_3761_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3767_, lean_object* v_as_3768_, lean_object* v_as_x27_3769_, lean_object* v_b_3770_, lean_object* v_a_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3767_, v_as_3768_, v_as_x27_3769_, v_b_3770_, v_a_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v_as_3768_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3776_, v_x_3777_, v_x_3778_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3783_, v_x_3784_, v_x_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3783_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3790_, v___y_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3800_, lean_object* v___x_3801_, lean_object* v___x_3802_, lean_object* v_inst_3803_, lean_object* v_R_3804_, lean_object* v_a_3805_, lean_object* v_b_3806_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3800_, v___x_3801_, v___x_3802_, v_a_3805_, v_b_3806_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3808_, lean_object* v___x_3809_, lean_object* v___x_3810_, lean_object* v_inst_3811_, lean_object* v_R_3812_, lean_object* v_a_3813_, lean_object* v_b_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3808_, v___x_3809_, v___x_3810_, v_inst_3811_, v_R_3812_, v_a_3813_, v_b_3814_);
lean_dec_ref(v___x_3809_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3816_, v___y_3818_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v_inst_3829_, lean_object* v_R_3830_, lean_object* v_a_3831_, lean_object* v_b_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3826_, v___x_3827_, v___x_3828_, v_a_3831_, v_b_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3834_, lean_object* v___x_3835_, lean_object* v___x_3836_, lean_object* v_inst_3837_, lean_object* v_R_3838_, lean_object* v_a_3839_, lean_object* v_b_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3834_, v___x_3835_, v___x_3836_, v_inst_3837_, v_R_3838_, v_a_3839_, v_b_3840_);
lean_dec_ref(v___x_3835_);
return v_res_3841_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3842_, lean_object* v_inst_3843_, lean_object* v_R_3844_, lean_object* v_a_3845_, uint8_t v_b_3846_, lean_object* v_c_3847_){
_start:
{
uint8_t v___x_3848_; 
v___x_3848_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3842_, v_a_3845_, v_b_3846_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3849_, lean_object* v_inst_3850_, lean_object* v_R_3851_, lean_object* v_a_3852_, lean_object* v_b_3853_, lean_object* v_c_3854_){
_start:
{
uint8_t v_b_boxed_3855_; uint8_t v_res_3856_; lean_object* v_r_3857_; 
v_b_boxed_3855_ = lean_unbox(v_b_3853_);
v_res_3856_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3849_, v_inst_3850_, v_R_3851_, v_a_3852_, v_b_boxed_3855_, v_c_3854_);
lean_dec_ref(v_s_3849_);
v_r_3857_ = lean_box(v_res_3856_);
return v_r_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3858_, lean_object* v_ref_3859_, lean_object* v_msg_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3859_, v_msg_3860_, v___y_3861_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3865_, lean_object* v_ref_3866_, lean_object* v_msg_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3865_, v_ref_3866_, v_msg_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v_ref_3866_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3872_, lean_object* v_as_x27_3873_, lean_object* v_b_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3873_, v_b_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3877_, lean_object* v_as_x27_3878_, lean_object* v_b_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3877_, v_as_x27_3878_, v_b_3879_, v_a_3880_);
lean_dec(v_as_3877_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3882_, lean_object* v_rsize_3883_, lean_object* v_histogram_3884_, lean_object* v_index_3885_, lean_object* v_val_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3884_, v_index_3885_, v_val_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3888_, lean_object* v_rsize_3889_, lean_object* v_histogram_3890_, lean_object* v_index_3891_, lean_object* v_val_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3888_, v_rsize_3889_, v_histogram_3890_, v_index_3891_, v_val_3892_);
lean_dec(v_rsize_3889_);
lean_dec(v_lsize_3888_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3894_, lean_object* v___x_3895_, lean_object* v_fst_3896_, lean_object* v___x_3897_, lean_object* v_inst_3898_, lean_object* v_R_3899_, lean_object* v_a_3900_, lean_object* v_b_3901_, lean_object* v_c_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3894_, v___x_3895_, v_fst_3896_, v___x_3897_, v_a_3900_, v_b_3901_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3904_, lean_object* v___x_3905_, lean_object* v_fst_3906_, lean_object* v___x_3907_, lean_object* v_inst_3908_, lean_object* v_R_3909_, lean_object* v_a_3910_, lean_object* v_b_3911_, lean_object* v_c_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3904_, v___x_3905_, v_fst_3906_, v___x_3907_, v_inst_3908_, v_R_3909_, v_a_3910_, v_b_3911_, v_c_3912_);
lean_dec(v___x_3907_);
lean_dec_ref(v_fst_3906_);
lean_dec(v___x_3905_);
lean_dec(v_upperBound_3904_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_3914_, lean_object* v_rsize_3915_, lean_object* v_histogram_3916_, lean_object* v_index_3917_, lean_object* v_val_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_3916_, v_index_3917_, v_val_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_3920_, lean_object* v_rsize_3921_, lean_object* v_histogram_3922_, lean_object* v_index_3923_, lean_object* v_val_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_3920_, v_rsize_3921_, v_histogram_3922_, v_index_3923_, v_val_3924_);
lean_dec(v_rsize_3921_);
lean_dec(v_lsize_3920_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_3926_, lean_object* v_fst_3927_, lean_object* v___x_3928_, lean_object* v_fst_3929_, lean_object* v_inst_3930_, lean_object* v_R_3931_, lean_object* v_a_3932_, lean_object* v_b_3933_, lean_object* v_c_3934_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3926_, v_fst_3927_, v___x_3928_, v_fst_3929_, v_a_3932_, v_b_3933_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_3936_, lean_object* v_fst_3937_, lean_object* v___x_3938_, lean_object* v_fst_3939_, lean_object* v_inst_3940_, lean_object* v_R_3941_, lean_object* v_a_3942_, lean_object* v_b_3943_, lean_object* v_c_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_3936_, v_fst_3937_, v___x_3938_, v_fst_3939_, v_inst_3940_, v_R_3941_, v_a_3942_, v_b_3943_, v_c_3944_);
lean_dec_ref(v_fst_3939_);
lean_dec(v___x_3938_);
lean_dec_ref(v_fst_3937_);
lean_dec(v_upperBound_3936_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_3946_, lean_object* v_msg_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_3947_, v___y_3948_, v___y_3949_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_3952_, lean_object* v_msg_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_3952_, v_msg_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_3958_, lean_object* v_m_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_3959_, v_a_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_3962_, lean_object* v_m_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_3962_, v_m_3963_, v_a_3964_);
lean_dec_ref(v_a_3964_);
lean_dec_ref(v_m_3963_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_3966_, lean_object* v_m_3967_, lean_object* v_a_3968_, lean_object* v_b_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_3967_, v_a_3968_, v_b_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_3971_, lean_object* v_macroStack_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_3971_, v_macroStack_3972_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_3977_, lean_object* v_macroStack_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_3977_, v_macroStack_3978_, v___y_3979_, v___y_3980_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_3983_, lean_object* v_R_3984_, lean_object* v_a_3985_, lean_object* v_b_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_3985_, v_b_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_3988_, lean_object* v_a_3989_, lean_object* v_x_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_3989_, v_x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_3992_, lean_object* v_a_3993_, lean_object* v_x_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_3992_, v_a_3993_, v_x_3994_);
lean_dec(v_x_3994_);
lean_dec_ref(v_a_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_3996_, lean_object* v_a_3997_, lean_object* v_x_3998_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_3997_, v_x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4000_, lean_object* v_a_4001_, lean_object* v_x_4002_){
_start:
{
uint8_t v_res_4003_; lean_object* v_r_4004_; 
v_res_4003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4000_, v_a_4001_, v_x_4002_);
lean_dec(v_x_4002_);
lean_dec_ref(v_a_4001_);
v_r_4004_ = lean_box(v_res_4003_);
return v_r_4004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4005_, lean_object* v_data_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4008_, lean_object* v_a_4009_, lean_object* v_b_4010_, lean_object* v_x_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4009_, v_b_4010_, v_x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4013_, lean_object* v_i_4014_, lean_object* v_source_4015_, lean_object* v_target_4016_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4014_, v_source_4015_, v_target_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4018_, lean_object* v_x_4019_, lean_object* v_x_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4019_, v_x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4030_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4031_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4033_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4034_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4064_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4065_ = l_Lean_addBuiltinDeclarationRanges(v___x_4063_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4068_){
_start:
{
lean_object* v_doc_4070_; lean_object* v___x_4071_; 
v_doc_4070_ = lean_ctor_get(v___y_4068_, 1);
lean_inc_ref(v_doc_4070_);
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v_doc_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4072_);
lean_dec_ref(v___y_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4075_, lean_object* v_a_4076_, uint8_t v_b_4077_){
_start:
{
lean_object* v_str_4078_; lean_object* v_startInclusive_4079_; lean_object* v_endExclusive_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_str_4078_ = lean_ctor_get(v_s_4075_, 0);
v_startInclusive_4079_ = lean_ctor_get(v_s_4075_, 1);
v_endExclusive_4080_ = lean_ctor_get(v_s_4075_, 2);
v___x_4081_ = lean_nat_sub(v_endExclusive_4080_, v_startInclusive_4079_);
v___x_4082_ = lean_nat_dec_eq(v_a_4076_, v___x_4081_);
lean_dec(v___x_4081_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; uint32_t v___x_4084_; uint32_t v___x_4085_; uint8_t v___x_4086_; 
v___x_4083_ = lean_nat_add(v_startInclusive_4079_, v_a_4076_);
lean_dec(v_a_4076_);
v___x_4084_ = lean_string_utf8_get_fast(v_str_4078_, v___x_4083_);
v___x_4085_ = 10;
v___x_4086_ = lean_uint32_dec_eq(v___x_4084_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_string_utf8_next_fast(v_str_4078_, v___x_4083_);
lean_dec(v___x_4083_);
v___x_4088_ = lean_nat_sub(v___x_4087_, v_startInclusive_4079_);
v_a_4076_ = v___x_4088_;
v_b_4077_ = v___x_4086_;
goto _start;
}
else
{
lean_dec(v___x_4083_);
return v___x_4086_;
}
}
else
{
lean_dec(v_a_4076_);
return v_b_4077_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4090_, lean_object* v_a_4091_, lean_object* v_b_4092_){
_start:
{
uint8_t v_b_boxed_4093_; uint8_t v_res_4094_; lean_object* v_r_4095_; 
v_b_boxed_4093_ = lean_unbox(v_b_4092_);
v_res_4094_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4090_, v_a_4091_, v_b_boxed_4093_);
lean_dec_ref(v_s_4090_);
v_r_4095_ = lean_box(v_res_4094_);
return v_r_4095_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4096_){
_start:
{
lean_object* v_searcher_4097_; uint8_t v___x_4098_; uint8_t v___x_4099_; 
v_searcher_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = 0;
v___x_4099_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4096_, v_searcher_4097_, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4100_){
_start:
{
uint8_t v_res_4101_; lean_object* v_r_4102_; 
v_res_4101_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4100_);
lean_dec_ref(v_s_4100_);
v_r_4102_ = lean_box(v_res_4101_);
return v_r_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4114_, lean_object* v_fst_4115_, uint8_t v___x_4116_, lean_object* v_a_4117_, lean_object* v___x_4118_, lean_object* v___x_4119_, lean_object* v___x_4120_, lean_object* v___x_4121_, lean_object* v___x_4122_, lean_object* v___x_4123_, lean_object* v___x_4124_, lean_object* v___x_4125_, lean_object* v_snd_4126_, lean_object* v___x_4127_){
_start:
{
if (lean_obj_tag(v___x_4114_) == 1)
{
lean_object* v_val_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4192_; 
v_val_4129_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4131_ = v___x_4114_;
v_isShared_4132_ = v_isSharedCheck_4192_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_val_4129_);
lean_dec(v___x_4114_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4192_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4133_ = lean_unsigned_to_nat(0u);
v___x_4134_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4135_ = l_Lean_Syntax_setArg(v_fst_4115_, v___x_4133_, v___x_4134_);
v___x_4136_ = l_Lean_Syntax_getPos_x3f(v___x_4135_, v___x_4116_);
lean_dec(v___x_4135_);
if (lean_obj_tag(v___x_4136_) == 1)
{
lean_object* v_val_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref(v___x_4127_);
v_val_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4188_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_val_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4188_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___y_4142_; lean_object* v___x_4168_; uint8_t v___y_4175_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4168_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4126_);
v___x_4180_ = lean_string_utf8_byte_size(v___x_4168_);
v___x_4181_ = lean_nat_dec_eq(v___x_4180_, v___x_4133_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4182_ = lean_string_length(v___x_4168_);
v___x_4183_ = lean_unsigned_to_nat(93u);
v___x_4184_ = lean_nat_dec_le(v___x_4182_, v___x_4183_);
if (v___x_4184_ == 0)
{
v___y_4175_ = v___x_4184_;
goto v___jp_4174_;
}
else
{
lean_object* v___x_4185_; uint8_t v___x_4186_; 
lean_inc_ref(v___x_4168_);
v___x_4185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4168_);
lean_ctor_set(v___x_4185_, 1, v___x_4133_);
lean_ctor_set(v___x_4185_, 2, v___x_4180_);
v___x_4186_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4185_);
lean_dec_ref(v___x_4185_);
if (v___x_4186_ == 0)
{
v___y_4175_ = v___x_4184_;
goto v___jp_4174_;
}
else
{
goto v___jp_4169_;
}
}
}
else
{
lean_object* v___x_4187_; 
lean_dec_ref(v___x_4168_);
v___x_4187_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4142_ = v___x_4187_;
goto v___jp_4141_;
}
v___jp_4141_:
{
lean_object* v_toEditableDocumentCore_4143_; lean_object* v_meta_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4164_; 
v_toEditableDocumentCore_4143_ = lean_ctor_get(v_a_4117_, 0);
lean_inc_ref(v_toEditableDocumentCore_4143_);
v_meta_4144_ = lean_ctor_get(v_toEditableDocumentCore_4143_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_toEditableDocumentCore_4143_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; lean_object* v_unused_4166_; lean_object* v_unused_4167_; 
v_unused_4165_ = lean_ctor_get(v_toEditableDocumentCore_4143_, 3);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_toEditableDocumentCore_4143_, 2);
lean_dec(v_unused_4166_);
v_unused_4167_ = lean_ctor_get(v_toEditableDocumentCore_4143_, 1);
lean_dec(v_unused_4167_);
v___x_4146_ = v_toEditableDocumentCore_4143_;
v_isShared_4147_ = v_isSharedCheck_4164_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_meta_4144_);
lean_dec(v_toEditableDocumentCore_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4164_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v_text_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4154_; 
v_text_4148_ = lean_ctor_get(v_meta_4144_, 3);
lean_inc_ref(v_text_4148_);
lean_dec_ref(v_meta_4144_);
v___x_4149_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4117_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v_val_4129_);
lean_ctor_set(v___x_4150_, 1, v_val_4137_);
v___x_4151_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4148_, v___x_4150_);
v___x_4152_ = lean_box(0);
lean_inc(v___x_4118_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 3, v___x_4118_);
lean_ctor_set(v___x_4146_, 2, v___x_4152_);
lean_ctor_set(v___x_4146_, 1, v___y_4142_);
lean_ctor_set(v___x_4146_, 0, v___x_4151_);
v___x_4154_ = v___x_4146_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4151_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v___y_4142_);
lean_ctor_set(v_reuseFailAlloc_4163_, 2, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4163_, 3, v___x_4118_);
v___x_4154_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4155_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4149_, v___x_4154_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4155_);
v___x_4157_ = v___x_4139_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_inc(v___x_4118_);
v___x_4158_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4118_);
lean_ctor_set(v___x_4158_, 1, v___x_4118_);
lean_ctor_set(v___x_4158_, 2, v___x_4119_);
lean_ctor_set(v___x_4158_, 3, v___x_4120_);
lean_ctor_set(v___x_4158_, 4, v___x_4121_);
lean_ctor_set(v___x_4158_, 5, v___x_4122_);
lean_ctor_set(v___x_4158_, 6, v___x_4123_);
lean_ctor_set(v___x_4158_, 7, v___x_4157_);
lean_ctor_set(v___x_4158_, 8, v___x_4124_);
lean_ctor_set(v___x_4158_, 9, v___x_4125_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4158_);
v___x_4160_ = v___x_4131_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
v___jp_4169_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4170_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4171_ = lean_string_append(v___x_4170_, v___x_4168_);
lean_dec_ref(v___x_4168_);
v___x_4172_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4173_ = lean_string_append(v___x_4171_, v___x_4172_);
v___y_4142_ = v___x_4173_;
goto v___jp_4141_;
}
v___jp_4174_:
{
if (v___y_4175_ == 0)
{
goto v___jp_4169_;
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4176_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4177_ = lean_string_append(v___x_4176_, v___x_4168_);
lean_dec_ref(v___x_4168_);
v___x_4178_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4179_ = lean_string_append(v___x_4177_, v___x_4178_);
v___y_4142_ = v___x_4179_;
goto v___jp_4141_;
}
}
}
}
else
{
lean_object* v___x_4190_; 
lean_dec(v___x_4136_);
lean_dec(v_val_4129_);
lean_dec_ref(v_snd_4126_);
lean_dec(v___x_4125_);
lean_dec(v___x_4124_);
lean_dec(v___x_4123_);
lean_dec(v___x_4122_);
lean_dec(v___x_4121_);
lean_dec(v___x_4120_);
lean_dec_ref(v___x_4119_);
lean_dec(v___x_4118_);
lean_dec_ref(v_a_4117_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4127_);
v___x_4190_ = v___x_4131_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4127_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v___x_4193_; 
lean_dec_ref(v_snd_4126_);
lean_dec(v___x_4125_);
lean_dec(v___x_4124_);
lean_dec(v___x_4123_);
lean_dec(v___x_4122_);
lean_dec(v___x_4121_);
lean_dec(v___x_4120_);
lean_dec_ref(v___x_4119_);
lean_dec(v___x_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_fst_4115_);
lean_dec(v___x_4114_);
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4127_);
return v___x_4193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4194_, lean_object* v_fst_4195_, lean_object* v___x_4196_, lean_object* v_a_4197_, lean_object* v___x_4198_, lean_object* v___x_4199_, lean_object* v___x_4200_, lean_object* v___x_4201_, lean_object* v___x_4202_, lean_object* v___x_4203_, lean_object* v___x_4204_, lean_object* v___x_4205_, lean_object* v_snd_4206_, lean_object* v___x_4207_, lean_object* v___y_4208_){
_start:
{
uint8_t v___x_4549__boxed_4209_; lean_object* v_res_4210_; 
v___x_4549__boxed_4209_ = lean_unbox(v___x_4196_);
v_res_4210_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4194_, v_fst_4195_, v___x_4549__boxed_4209_, v_a_4197_, v___x_4198_, v___x_4199_, v___x_4200_, v___x_4201_, v___x_4202_, v___x_4203_, v___x_4204_, v___x_4205_, v_snd_4206_, v___x_4207_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4214_, size_t v_sz_4215_, size_t v_i_4216_, lean_object* v_b_4217_){
_start:
{
lean_object* v_a_4219_; uint8_t v___x_4223_; 
v___x_4223_ = lean_usize_dec_lt(v_i_4216_, v_sz_4215_);
if (v___x_4223_ == 0)
{
lean_inc_ref(v_b_4217_);
return v_b_4217_;
}
else
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v_a_4226_; 
v___x_4224_ = lean_box(0);
v___x_4225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4226_ = lean_array_uget(v_as_4214_, v_i_4216_);
if (lean_obj_tag(v_a_4226_) == 1)
{
lean_object* v_i_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4261_; 
v_i_4227_ = lean_ctor_get(v_a_4226_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_a_4226_);
if (v_isSharedCheck_4261_ == 0)
{
lean_object* v_unused_4262_; 
v_unused_4262_ = lean_ctor_get(v_a_4226_, 1);
lean_dec(v_unused_4262_);
v___x_4229_ = v_a_4226_;
v_isShared_4230_ = v_isSharedCheck_4261_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_i_4227_);
lean_dec(v_a_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4261_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
if (lean_obj_tag(v_i_4227_) == 10)
{
lean_object* v_i_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4260_; 
v_i_4231_ = lean_ctor_get(v_i_4227_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_i_4227_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4233_ = v_i_4227_;
v_isShared_4234_ = v_isSharedCheck_4260_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_i_4231_);
lean_dec(v_i_4227_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4260_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v_stx_4235_; lean_object* v_value_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4259_; 
v_stx_4235_ = lean_ctor_get(v_i_4231_, 0);
v_value_4236_ = lean_ctor_get(v_i_4231_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_i_4231_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4238_ = v_i_4231_;
v_isShared_4239_ = v_isSharedCheck_4259_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_value_4236_);
lean_inc(v_stx_4235_);
lean_dec(v_i_4231_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4259_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4241_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4236_, v___x_4240_);
lean_dec(v_value_4236_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_del_object(v___x_4238_);
lean_dec(v_stx_4235_);
lean_del_object(v___x_4233_);
lean_del_object(v___x_4229_);
v_a_4219_ = v___x_4225_;
goto v___jp_4218_;
}
else
{
lean_object* v_val_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4258_; 
v_val_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4258_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_val_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4258_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 1, v_val_4242_);
v___x_4247_ = v___x_4238_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_stx_4235_);
lean_ctor_set(v_reuseFailAlloc_4257_, 1, v_val_4242_);
v___x_4247_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4249_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4247_);
v___x_4249_ = v___x_4244_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4251_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 1);
lean_ctor_set(v___x_4233_, 0, v___x_4249_);
v___x_4251_ = v___x_4233_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4253_; 
if (v_isShared_4230_ == 0)
{
lean_ctor_set_tag(v___x_4229_, 0);
lean_ctor_set(v___x_4229_, 1, v___x_4224_);
lean_ctor_set(v___x_4229_, 0, v___x_4251_);
v___x_4253_ = v___x_4229_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v___x_4224_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
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
lean_del_object(v___x_4229_);
lean_dec_ref(v_i_4227_);
v_a_4219_ = v___x_4225_;
goto v___jp_4218_;
}
}
}
else
{
lean_dec(v_a_4226_);
v_a_4219_ = v___x_4225_;
goto v___jp_4218_;
}
}
v___jp_4218_:
{
size_t v___x_4220_; size_t v___x_4221_; 
v___x_4220_ = ((size_t)1ULL);
v___x_4221_ = lean_usize_add(v_i_4216_, v___x_4220_);
v_i_4216_ = v___x_4221_;
v_b_4217_ = v_a_4219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4263_, lean_object* v_sz_4264_, lean_object* v_i_4265_, lean_object* v_b_4266_){
_start:
{
size_t v_sz_boxed_4267_; size_t v_i_boxed_4268_; lean_object* v_res_4269_; 
v_sz_boxed_4267_ = lean_unbox_usize(v_sz_4264_);
lean_dec(v_sz_4264_);
v_i_boxed_4268_ = lean_unbox_usize(v_i_4265_);
lean_dec(v_i_4265_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4263_, v_sz_boxed_4267_, v_i_boxed_4268_, v_b_4266_);
lean_dec_ref(v_b_4266_);
lean_dec_ref(v_as_4263_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4270_, size_t v_sz_4271_, size_t v_i_4272_, lean_object* v_b_4273_){
_start:
{
lean_object* v_a_4275_; uint8_t v___x_4279_; 
v___x_4279_ = lean_usize_dec_lt(v_i_4272_, v_sz_4271_);
if (v___x_4279_ == 0)
{
lean_inc_ref(v_b_4273_);
return v_b_4273_;
}
else
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v_a_4282_; 
v___x_4280_ = lean_box(0);
v___x_4281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4282_ = lean_array_uget(v_as_4270_, v_i_4272_);
if (lean_obj_tag(v_a_4282_) == 1)
{
lean_object* v_i_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4317_; 
v_i_4283_ = lean_ctor_get(v_a_4282_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_a_4282_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; 
v_unused_4318_ = lean_ctor_get(v_a_4282_, 1);
lean_dec(v_unused_4318_);
v___x_4285_ = v_a_4282_;
v_isShared_4286_ = v_isSharedCheck_4317_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_i_4283_);
lean_dec(v_a_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4317_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
if (lean_obj_tag(v_i_4283_) == 10)
{
lean_object* v_i_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4316_; 
v_i_4287_ = lean_ctor_get(v_i_4283_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_i_4283_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4289_ = v_i_4283_;
v_isShared_4290_ = v_isSharedCheck_4316_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_i_4287_);
lean_dec(v_i_4283_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4316_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v_stx_4291_; lean_object* v_value_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4315_; 
v_stx_4291_ = lean_ctor_get(v_i_4287_, 0);
v_value_4292_ = lean_ctor_get(v_i_4287_, 1);
v_isSharedCheck_4315_ = !lean_is_exclusive(v_i_4287_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4294_ = v_i_4287_;
v_isShared_4295_ = v_isSharedCheck_4315_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_value_4292_);
lean_inc(v_stx_4291_);
lean_dec(v_i_4287_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4315_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4297_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4292_, v___x_4296_);
lean_dec(v_value_4292_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_del_object(v___x_4294_);
lean_dec(v_stx_4291_);
lean_del_object(v___x_4289_);
lean_del_object(v___x_4285_);
v_a_4275_ = v___x_4281_;
goto v___jp_4274_;
}
else
{
lean_object* v_val_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4314_; 
v_val_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4314_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_val_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4314_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 1, v_val_4298_);
v___x_4303_ = v___x_4294_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_stx_4291_);
lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_val_4298_);
v___x_4303_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4305_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4303_);
v___x_4305_ = v___x_4300_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4307_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 1);
lean_ctor_set(v___x_4289_, 0, v___x_4305_);
v___x_4307_ = v___x_4289_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4309_; 
if (v_isShared_4286_ == 0)
{
lean_ctor_set_tag(v___x_4285_, 0);
lean_ctor_set(v___x_4285_, 1, v___x_4280_);
lean_ctor_set(v___x_4285_, 0, v___x_4307_);
v___x_4309_ = v___x_4285_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v___x_4280_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
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
lean_del_object(v___x_4285_);
lean_dec_ref(v_i_4283_);
v_a_4275_ = v___x_4281_;
goto v___jp_4274_;
}
}
}
else
{
lean_dec(v_a_4282_);
v_a_4275_ = v___x_4281_;
goto v___jp_4274_;
}
}
v___jp_4274_:
{
size_t v___x_4276_; size_t v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((size_t)1ULL);
v___x_4277_ = lean_usize_add(v_i_4272_, v___x_4276_);
v___x_4278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4270_, v_sz_4271_, v___x_4277_, v_a_4275_);
return v___x_4278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4319_, lean_object* v_sz_4320_, lean_object* v_i_4321_, lean_object* v_b_4322_){
_start:
{
size_t v_sz_boxed_4323_; size_t v_i_boxed_4324_; lean_object* v_res_4325_; 
v_sz_boxed_4323_ = lean_unbox_usize(v_sz_4320_);
lean_dec(v_sz_4320_);
v_i_boxed_4324_ = lean_unbox_usize(v_i_4321_);
lean_dec(v_i_4321_);
v_res_4325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4319_, v_sz_boxed_4323_, v_i_boxed_4324_, v_b_4322_);
lean_dec_ref(v_b_4322_);
lean_dec_ref(v_as_4319_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4326_){
_start:
{
if (lean_obj_tag(v_x_4326_) == 0)
{
lean_object* v_cs_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; size_t v_sz_4330_; size_t v___x_4331_; lean_object* v___x_4332_; lean_object* v_fst_4333_; 
v_cs_4327_ = lean_ctor_get(v_x_4326_, 0);
v___x_4328_ = lean_box(0);
v___x_4329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4330_ = lean_array_size(v_cs_4327_);
v___x_4331_ = ((size_t)0ULL);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4327_, v_sz_4330_, v___x_4331_, v___x_4329_);
v_fst_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_fst_4333_);
lean_dec_ref(v___x_4332_);
if (lean_obj_tag(v_fst_4333_) == 0)
{
return v___x_4328_;
}
else
{
lean_object* v_val_4334_; 
v_val_4334_ = lean_ctor_get(v_fst_4333_, 0);
lean_inc(v_val_4334_);
lean_dec_ref(v_fst_4333_);
return v_val_4334_;
}
}
else
{
lean_object* v_vs_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; size_t v_sz_4338_; size_t v___x_4339_; lean_object* v___x_4340_; lean_object* v_fst_4341_; 
v_vs_4335_ = lean_ctor_get(v_x_4326_, 0);
v___x_4336_ = lean_box(0);
v___x_4337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4338_ = lean_array_size(v_vs_4335_);
v___x_4339_ = ((size_t)0ULL);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4335_, v_sz_4338_, v___x_4339_, v___x_4337_);
v_fst_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_fst_4341_);
lean_dec_ref(v___x_4340_);
if (lean_obj_tag(v_fst_4341_) == 0)
{
return v___x_4336_;
}
else
{
lean_object* v_val_4342_; 
v_val_4342_ = lean_ctor_get(v_fst_4341_, 0);
lean_inc(v_val_4342_);
lean_dec_ref(v_fst_4341_);
return v_val_4342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4343_, size_t v_sz_4344_, size_t v_i_4345_, lean_object* v_b_4346_){
_start:
{
uint8_t v___x_4347_; 
v___x_4347_ = lean_usize_dec_lt(v_i_4345_, v_sz_4344_);
if (v___x_4347_ == 0)
{
lean_inc_ref(v_b_4346_);
return v_b_4346_;
}
else
{
lean_object* v___x_4348_; lean_object* v_a_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_box(0);
v_a_4349_ = lean_array_uget_borrowed(v_as_4343_, v_i_4345_);
v___x_4350_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4349_);
if (lean_obj_tag(v___x_4350_) == 1)
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
lean_ctor_set(v___x_4352_, 1, v___x_4348_);
return v___x_4352_;
}
else
{
lean_object* v___x_4353_; size_t v___x_4354_; size_t v___x_4355_; 
lean_dec(v___x_4350_);
v___x_4353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4354_ = ((size_t)1ULL);
v___x_4355_ = lean_usize_add(v_i_4345_, v___x_4354_);
v_i_4345_ = v___x_4355_;
v_b_4346_ = v___x_4353_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4357_, lean_object* v_sz_4358_, lean_object* v_i_4359_, lean_object* v_b_4360_){
_start:
{
size_t v_sz_boxed_4361_; size_t v_i_boxed_4362_; lean_object* v_res_4363_; 
v_sz_boxed_4361_ = lean_unbox_usize(v_sz_4358_);
lean_dec(v_sz_4358_);
v_i_boxed_4362_ = lean_unbox_usize(v_i_4359_);
lean_dec(v_i_4359_);
v_res_4363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4357_, v_sz_boxed_4361_, v_i_boxed_4362_, v_b_4360_);
lean_dec_ref(v_b_4360_);
lean_dec_ref(v_as_4357_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4364_);
lean_dec_ref(v_x_4364_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4366_){
_start:
{
lean_object* v_root_4367_; lean_object* v_tail_4368_; lean_object* v___x_4369_; 
v_root_4367_ = lean_ctor_get(v_t_4366_, 0);
v_tail_4368_ = lean_ctor_get(v_t_4366_, 1);
v___x_4369_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4367_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v___x_4370_; size_t v_sz_4371_; size_t v___x_4372_; lean_object* v___x_4373_; lean_object* v_fst_4374_; 
v___x_4370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4371_ = lean_array_size(v_tail_4368_);
v___x_4372_ = ((size_t)0ULL);
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4368_, v_sz_4371_, v___x_4372_, v___x_4370_);
v_fst_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_fst_4374_);
lean_dec_ref(v___x_4373_);
if (lean_obj_tag(v_fst_4374_) == 0)
{
return v___x_4369_;
}
else
{
lean_object* v_val_4375_; 
v_val_4375_ = lean_ctor_get(v_fst_4374_, 0);
lean_inc(v_val_4375_);
lean_dec_ref(v_fst_4374_);
return v_val_4375_;
}
}
else
{
return v___x_4369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4376_);
lean_dec_ref(v_t_4376_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4392_, lean_object* v_a_4393_){
_start:
{
if (lean_obj_tag(v_node_4392_) == 1)
{
lean_object* v_children_4395_; lean_object* v_res_4396_; 
v_children_4395_ = lean_ctor_get(v_node_4392_, 1);
v_res_4396_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4395_);
if (lean_obj_tag(v_res_4396_) == 1)
{
lean_object* v_val_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4434_; 
v_val_4397_ = lean_ctor_get(v_res_4396_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_res_4396_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4399_ = v_res_4396_;
v_isShared_4400_ = v_isSharedCheck_4434_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_val_4397_);
lean_dec(v_res_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4434_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v_fst_4401_; lean_object* v_snd_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4433_; 
v_fst_4401_ = lean_ctor_get(v_val_4397_, 0);
v_snd_4402_ = lean_ctor_get(v_val_4397_, 1);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_val_4397_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4404_ = v_val_4397_;
v_isShared_4405_ = v_isSharedCheck_4433_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_snd_4402_);
lean_inc(v_fst_4401_);
lean_dec(v_val_4397_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4433_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4432_; 
v___x_4406_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4393_);
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4432_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4432_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___y_4419_; lean_object* v___x_4421_; 
v___x_4411_ = lean_box(0);
v___x_4412_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4413_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4414_ = 1;
v___x_4415_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4416_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4417_ = l_Lean_Syntax_getPos_x3f(v_fst_4401_, v___x_4414_);
v___x_4418_ = lean_box(v___x_4414_);
v___y_4419_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4419_, 0, v___x_4417_);
lean_closure_set(v___y_4419_, 1, v_fst_4401_);
lean_closure_set(v___y_4419_, 2, v___x_4418_);
lean_closure_set(v___y_4419_, 3, v_a_4407_);
lean_closure_set(v___y_4419_, 4, v___x_4411_);
lean_closure_set(v___y_4419_, 5, v___x_4412_);
lean_closure_set(v___y_4419_, 6, v___x_4413_);
lean_closure_set(v___y_4419_, 7, v___x_4411_);
lean_closure_set(v___y_4419_, 8, v___x_4415_);
lean_closure_set(v___y_4419_, 9, v___x_4411_);
lean_closure_set(v___y_4419_, 10, v___x_4411_);
lean_closure_set(v___y_4419_, 11, v___x_4411_);
lean_closure_set(v___y_4419_, 12, v_snd_4402_);
lean_closure_set(v___y_4419_, 13, v___x_4416_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v___y_4419_);
v___x_4421_ = v___x_4399_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___y_4419_);
v___x_4421_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4423_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 1, v___x_4421_);
lean_ctor_set(v___x_4404_, 0, v___x_4416_);
v___x_4423_ = v___x_4404_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4428_; 
v___x_4424_ = lean_unsigned_to_nat(1u);
v___x_4425_ = lean_mk_empty_array_with_capacity(v___x_4424_);
v___x_4426_ = lean_array_push(v___x_4425_, v___x_4423_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4426_);
v___x_4428_ = v___x_4409_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_dec(v_res_4396_);
v___x_4435_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
return v___x_4438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4439_, v_a_4440_);
lean_dec_ref(v_a_4440_);
lean_dec_ref(v_node_4439_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4443_, lean_object* v_x_4444_, lean_object* v_x_4445_, lean_object* v_node_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4446_, v_a_4447_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4450_, lean_object* v_x_4451_, lean_object* v_x_4452_, lean_object* v_node_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4450_, v_x_4451_, v_x_4452_, v_node_4453_, v_a_4454_);
lean_dec_ref(v_a_4454_);
lean_dec_ref(v_node_4453_);
lean_dec_ref(v_x_4452_);
lean_dec_ref(v_x_4451_);
lean_dec_ref(v_x_4450_);
return v_res_4456_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4457_, lean_object* v_inst_4458_, lean_object* v_R_4459_, lean_object* v_a_4460_, uint8_t v_b_4461_, lean_object* v_c_4462_){
_start:
{
uint8_t v___x_4463_; 
v___x_4463_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4457_, v_a_4460_, v_b_4461_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4464_, lean_object* v_inst_4465_, lean_object* v_R_4466_, lean_object* v_a_4467_, lean_object* v_b_4468_, lean_object* v_c_4469_){
_start:
{
uint8_t v_b_boxed_4470_; uint8_t v_res_4471_; lean_object* v_r_4472_; 
v_b_boxed_4470_ = lean_unbox(v_b_4468_);
v_res_4471_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4464_, v_inst_4465_, v_R_4466_, v_a_4467_, v_b_boxed_4470_, v_c_4469_);
lean_dec_ref(v_s_4464_);
v_r_4472_ = lean_box(v_res_4471_);
return v_r_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_(){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_));
v___x_4479_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4480_ = l_Lean_CodeAction_insertBuiltin(v___x_4478_, v___x_4479_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369____boxed(lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_369_();
return v_res_4482_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4484_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4485_ = lean_string_utf8_byte_size(v___x_4484_);
return v___x_4485_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4486_ = lean_unsigned_to_nat(0u);
v___x_4487_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4488_ = lean_nat_dec_eq(v___x_4487_, v___x_4486_);
return v___x_4488_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4489_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4490_ = lean_unsigned_to_nat(0u);
v___x_4491_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v___x_4490_);
lean_ctor_set(v___x_4492_, 2, v___x_4489_);
return v___x_4492_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4494_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4493_);
return v___x_4494_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4495_ = lean_unsigned_to_nat(0u);
v___x_4496_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4497_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4498_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
lean_ctor_set(v___x_4498_, 1, v___x_4496_);
lean_ctor_set(v___x_4498_, 2, v___x_4495_);
lean_ctor_set(v___x_4498_, 3, v___x_4495_);
return v___x_4498_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4499_){
_start:
{
lean_object* v___y_4501_; uint8_t v___x_4504_; 
v___x_4504_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4501_ = v___x_4505_;
goto v___jp_4500_;
}
else
{
lean_object* v___x_4506_; 
v___x_4506_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4501_ = v___x_4506_;
goto v___jp_4500_;
}
v___jp_4500_:
{
uint8_t v___x_4502_; uint8_t v___x_4503_; 
v___x_4502_ = 0;
lean_inc(v___y_4501_);
v___x_4503_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4499_, v___y_4501_, v___x_4502_);
return v___x_4503_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4507_){
_start:
{
uint8_t v_res_4508_; lean_object* v_r_4509_; 
v_res_4508_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4507_);
lean_dec_ref(v_s_4507_);
v_r_4509_ = lean_box(v_res_4508_);
return v_r_4509_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4510_, lean_object* v_as_x27_4511_, uint8_t v_b_4512_){
_start:
{
if (lean_obj_tag(v_as_x27_4511_) == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = lean_box(v_b_4512_);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
return v___x_4515_;
}
else
{
lean_object* v_head_4516_; uint8_t v_isSilent_4517_; 
v_head_4516_ = lean_ctor_get(v_as_x27_4511_, 0);
v_isSilent_4517_ = lean_ctor_get_uint8(v_head_4516_, sizeof(void*)*5 + 2);
if (v_isSilent_4517_ == 0)
{
lean_object* v_tail_4518_; lean_object* v_data_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; uint8_t v___x_4524_; 
lean_inc(v_head_4516_);
v_tail_4518_ = lean_ctor_get(v_as_x27_4511_, 1);
lean_inc(v_tail_4518_);
lean_dec_ref(v_as_x27_4511_);
v_data_4519_ = lean_ctor_get(v_head_4516_, 4);
lean_inc(v_data_4519_);
lean_dec(v_head_4516_);
v___x_4520_ = l_Lean_MessageData_toString(v_data_4519_);
v___x_4521_ = lean_unsigned_to_nat(0u);
v___x_4522_ = lean_string_utf8_byte_size(v___x_4520_);
v___x_4523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4520_);
lean_ctor_set(v___x_4523_, 1, v___x_4521_);
lean_ctor_set(v___x_4523_, 2, v___x_4522_);
v___x_4524_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4523_);
lean_dec_ref(v___x_4523_);
if (v___x_4524_ == 0)
{
v_as_x27_4511_ = v_tail_4518_;
goto _start;
}
else
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
lean_dec(v_tail_4518_);
v___x_4526_ = lean_box(v_foundPanic_4510_);
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
return v___x_4527_;
}
}
else
{
lean_object* v_tail_4528_; 
v_tail_4528_ = lean_ctor_get(v_as_x27_4511_, 1);
lean_inc(v_tail_4528_);
lean_dec_ref(v_as_x27_4511_);
v_as_x27_4511_ = v_tail_4528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4530_, lean_object* v_as_x27_4531_, lean_object* v_b_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v_foundPanic_boxed_4534_; uint8_t v_b_boxed_4535_; lean_object* v_res_4536_; 
v_foundPanic_boxed_4534_ = lean_unbox(v_foundPanic_4530_);
v_b_boxed_4535_ = lean_unbox(v_b_4532_);
v_res_4536_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4534_, v_as_x27_4531_, v_b_boxed_4535_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4537_, uint8_t v_severity_4538_, uint8_t v_isSilent_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = l_Lean_Elab_Command_getRef___redArg(v___y_4540_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4545_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc(v_a_4544_);
lean_dec_ref(v___x_4543_);
v___x_4545_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4544_, v_msgData_4537_, v_severity_4538_, v_isSilent_4539_, v___y_4540_, v___y_4541_);
lean_dec(v_a_4544_);
return v___x_4545_;
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec_ref(v_msgData_4537_);
v_a_4546_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4543_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4543_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4554_, lean_object* v_severity_4555_, lean_object* v_isSilent_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
uint8_t v_severity_boxed_4560_; uint8_t v_isSilent_boxed_4561_; lean_object* v_res_4562_; 
v_severity_boxed_4560_ = lean_unbox(v_severity_4555_);
v_isSilent_boxed_4561_ = lean_unbox(v_isSilent_4556_);
v_res_4562_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4554_, v_severity_boxed_4560_, v_isSilent_boxed_4561_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
uint8_t v___x_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = 2;
v___x_4568_ = 0;
v___x_4569_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4563_, v___x_4567_, v___x_4568_, v___y_4564_, v___y_4565_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
return v_res_4574_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4583_ = l_Lean_MessageData_ofFormat(v___x_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v___x_4588_; uint8_t v_foundPanic_4589_; 
v___x_4588_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4584_);
v_foundPanic_4589_ = l_Lean_Syntax_isOfKind(v_x_4584_, v___x_4588_);
if (v_foundPanic_4589_ == 0)
{
lean_object* v___x_4590_; 
lean_dec(v_x_4584_);
v___x_4590_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4590_;
}
else
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4591_ = lean_unsigned_to_nat(2u);
v___x_4592_ = l_Lean_Syntax_getArg(v_x_4584_, v___x_4591_);
lean_dec(v_x_4584_);
v___x_4593_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4592_, v_a_4585_, v_a_4586_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; uint8_t v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4650_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4593_);
v___x_4595_ = 0;
v___x_4596_ = l_Lean_MessageLog_toList(v_a_4594_);
v___x_4597_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4589_, v___x_4596_, v___x_4595_);
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4650_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4650_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_unbox(v_a_4598_);
lean_dec(v_a_4598_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v_env_4604_; lean_object* v_scopes_4605_; lean_object* v_usedQuotCtxts_4606_; lean_object* v_nextMacroScope_4607_; lean_object* v_maxRecDepth_4608_; lean_object* v_ngen_4609_; lean_object* v_auxDeclNGen_4610_; lean_object* v_infoState_4611_; lean_object* v_traceState_4612_; lean_object* v_snapshotTasks_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4623_; 
lean_del_object(v___x_4600_);
v___x_4603_ = lean_st_ref_take(v_a_4586_);
v_env_4604_ = lean_ctor_get(v___x_4603_, 0);
v_scopes_4605_ = lean_ctor_get(v___x_4603_, 2);
v_usedQuotCtxts_4606_ = lean_ctor_get(v___x_4603_, 3);
v_nextMacroScope_4607_ = lean_ctor_get(v___x_4603_, 4);
v_maxRecDepth_4608_ = lean_ctor_get(v___x_4603_, 5);
v_ngen_4609_ = lean_ctor_get(v___x_4603_, 6);
v_auxDeclNGen_4610_ = lean_ctor_get(v___x_4603_, 7);
v_infoState_4611_ = lean_ctor_get(v___x_4603_, 8);
v_traceState_4612_ = lean_ctor_get(v___x_4603_, 9);
v_snapshotTasks_4613_ = lean_ctor_get(v___x_4603_, 10);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4623_ == 0)
{
lean_object* v_unused_4624_; 
v_unused_4624_ = lean_ctor_get(v___x_4603_, 1);
lean_dec(v_unused_4624_);
v___x_4615_ = v___x_4603_;
v_isShared_4616_ = v_isSharedCheck_4623_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_snapshotTasks_4613_);
lean_inc(v_traceState_4612_);
lean_inc(v_infoState_4611_);
lean_inc(v_auxDeclNGen_4610_);
lean_inc(v_ngen_4609_);
lean_inc(v_maxRecDepth_4608_);
lean_inc(v_nextMacroScope_4607_);
lean_inc(v_usedQuotCtxts_4606_);
lean_inc(v_scopes_4605_);
lean_inc(v_env_4604_);
lean_dec(v___x_4603_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4623_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 1, v_a_4594_);
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_env_4604_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_a_4594_);
lean_ctor_set(v_reuseFailAlloc_4622_, 2, v_scopes_4605_);
lean_ctor_set(v_reuseFailAlloc_4622_, 3, v_usedQuotCtxts_4606_);
lean_ctor_set(v_reuseFailAlloc_4622_, 4, v_nextMacroScope_4607_);
lean_ctor_set(v_reuseFailAlloc_4622_, 5, v_maxRecDepth_4608_);
lean_ctor_set(v_reuseFailAlloc_4622_, 6, v_ngen_4609_);
lean_ctor_set(v_reuseFailAlloc_4622_, 7, v_auxDeclNGen_4610_);
lean_ctor_set(v_reuseFailAlloc_4622_, 8, v_infoState_4611_);
lean_ctor_set(v_reuseFailAlloc_4622_, 9, v_traceState_4612_);
lean_ctor_set(v_reuseFailAlloc_4622_, 10, v_snapshotTasks_4613_);
v___x_4618_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = lean_st_ref_set(v_a_4586_, v___x_4618_);
v___x_4620_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4621_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4620_, v_a_4585_, v_a_4586_);
return v___x_4621_;
}
}
}
else
{
lean_object* v___x_4625_; lean_object* v_env_4626_; lean_object* v_scopes_4627_; lean_object* v_usedQuotCtxts_4628_; lean_object* v_nextMacroScope_4629_; lean_object* v_maxRecDepth_4630_; lean_object* v_ngen_4631_; lean_object* v_auxDeclNGen_4632_; lean_object* v_infoState_4633_; lean_object* v_traceState_4634_; lean_object* v_snapshotTasks_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4648_; 
lean_dec(v_a_4594_);
v___x_4625_ = lean_st_ref_take(v_a_4586_);
v_env_4626_ = lean_ctor_get(v___x_4625_, 0);
v_scopes_4627_ = lean_ctor_get(v___x_4625_, 2);
v_usedQuotCtxts_4628_ = lean_ctor_get(v___x_4625_, 3);
v_nextMacroScope_4629_ = lean_ctor_get(v___x_4625_, 4);
v_maxRecDepth_4630_ = lean_ctor_get(v___x_4625_, 5);
v_ngen_4631_ = lean_ctor_get(v___x_4625_, 6);
v_auxDeclNGen_4632_ = lean_ctor_get(v___x_4625_, 7);
v_infoState_4633_ = lean_ctor_get(v___x_4625_, 8);
v_traceState_4634_ = lean_ctor_get(v___x_4625_, 9);
v_snapshotTasks_4635_ = lean_ctor_get(v___x_4625_, 10);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4648_ == 0)
{
lean_object* v_unused_4649_; 
v_unused_4649_ = lean_ctor_get(v___x_4625_, 1);
lean_dec(v_unused_4649_);
v___x_4637_ = v___x_4625_;
v_isShared_4638_ = v_isSharedCheck_4648_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_snapshotTasks_4635_);
lean_inc(v_traceState_4634_);
lean_inc(v_infoState_4633_);
lean_inc(v_auxDeclNGen_4632_);
lean_inc(v_ngen_4631_);
lean_inc(v_maxRecDepth_4630_);
lean_inc(v_nextMacroScope_4629_);
lean_inc(v_usedQuotCtxts_4628_);
lean_inc(v_scopes_4627_);
lean_inc(v_env_4626_);
lean_dec(v___x_4625_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4648_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4639_ = l_Lean_MessageLog_empty;
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 1, v___x_4639_);
v___x_4641_ = v___x_4637_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_env_4626_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4647_, 2, v_scopes_4627_);
lean_ctor_set(v_reuseFailAlloc_4647_, 3, v_usedQuotCtxts_4628_);
lean_ctor_set(v_reuseFailAlloc_4647_, 4, v_nextMacroScope_4629_);
lean_ctor_set(v_reuseFailAlloc_4647_, 5, v_maxRecDepth_4630_);
lean_ctor_set(v_reuseFailAlloc_4647_, 6, v_ngen_4631_);
lean_ctor_set(v_reuseFailAlloc_4647_, 7, v_auxDeclNGen_4632_);
lean_ctor_set(v_reuseFailAlloc_4647_, 8, v_infoState_4633_);
lean_ctor_set(v_reuseFailAlloc_4647_, 9, v_traceState_4634_);
lean_ctor_set(v_reuseFailAlloc_4647_, 10, v_snapshotTasks_4635_);
v___x_4641_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4645_; 
v___x_4642_ = lean_st_ref_set(v_a_4586_, v___x_4641_);
v___x_4643_ = lean_box(0);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4643_);
v___x_4645_ = v___x_4600_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
v_a_4651_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4593_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4593_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4659_, v_a_4660_, v_a_4661_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4664_, lean_object* v_as_4665_, lean_object* v_as_x27_4666_, uint8_t v_b_4667_, lean_object* v_a_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4664_, v_as_x27_4666_, v_b_4667_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4673_, lean_object* v_as_4674_, lean_object* v_as_x27_4675_, lean_object* v_b_4676_, lean_object* v_a_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
uint8_t v_foundPanic_boxed_4681_; uint8_t v_b_boxed_4682_; lean_object* v_res_4683_; 
v_foundPanic_boxed_4681_ = lean_unbox(v_foundPanic_4673_);
v_b_boxed_4682_ = lean_unbox(v_b_4676_);
v_res_4683_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4681_, v_as_4674_, v_as_x27_4675_, v_b_boxed_4682_, v_a_4677_, v___y_4678_, v___y_4679_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v_as_4674_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4692_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4693_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4694_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4695_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4696_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4692_, v___x_4693_, v___x_4694_, v___x_4695_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4698_;
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
